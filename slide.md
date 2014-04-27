!SLIDE

# 型推論器とcore.logic

[@halcat0x15a](http://twitter.com/halcat0x15a)

!SLIDE

# 型推論器で式から型を導出する

```clojure
user> (require '[typelogic.core :refer [check]])
nil
user> (check 0)
(java.lang.Long)
user> (check '(let [a ""] a))
(java.lang.String)
user> (check '(fn [x y] x))
((:typelogic.core/fn _0 _0 _1))
```
`:typelogic.core/fn`は関数の型を表す

`(:typelogic.core/fn return-type parameter-types*)`

!SLIDE

# [core.logic](http://github.com/clojure/core.logic)

Clojureの論理プログラミングライブラリ

関係プログラミングや制約論理プログラミングなどサポート

!SLIDE

# 単一化

```clojure
user> 
(run* [q]
  (fresh [a b]
    (== q {:a a, :b b})
    (appendo [1] [2 3] a)
    (appendo [1] b [1 2 3])))
({:a (1 2 3), :b (2 3)})
```

* aは[1]と[2 3]を連結した値
* bは[1]と連結すると[1 2 3]となる値

!SLIDE

# バックトラッキング

```clojure
user> 
(run* [q]
  (fresh [x y]
    (== q {:x x, :y y})
    (appendo x y [1 2 3])))
({:x (), :y [1 2 3]} {:x (1), :y (2 3)} {:x (1 2), :y (3)} {:x (1 2 3), :y ()})
```

* xとyは連結すると[1 2 3]となる値
* 組み合わせの探索をしている

!SLIDE

# 論理プログラミングによる型付け規則の記述

構文, special formに対して型付け規則を記述する

```clojure
(defn ann [ctx expr type]
  (matcha [expr]
    ([['if test then]]
       (ann-if ctx test then nil type))
    ([['if test then else]]
       (ann-if ctx test then else type))
    ([['do . exprs]]
       (ann-do ctx exprs type))
    ([[_ . _]]
       (ann-app ctx expr type))))
```

!SLIDE

# doの型付け

```clojure
(defn ann-do [ctx exprs type]
  (matcha [exprs]
    ([[]] (== type nil))
    ([[expr]] (ann ctx expr type))
    ([[expr . exprs']]
       (fresh [type] (ann ctx expr type))
       (ann-do ctx exprs' type))))
```

!SLIDE

# ifの型付け

```clojure
(declare ann)

(defn ann-if [ctx test then else type]
  (fresh [then' else']
    (fresh [type] (ann ctx test type))
    (ann ctx then then')
    (ann ctx else else')
    (matche [type] ([then']) ([else']))))
```

!SLIDE

# 適用の型付け

```clojure
(defn ann-list [ctx exprs types]
  (matcha [exprs types]
    ([[] []])
    ([[expr . exprs'] [type . types']]
       (ann ctx expr type)
       (ann-list ctx exprs' types'))))

(defn ann-app [ctx exprs type]
  (fresh [types]
    (ann-list ctx exprs types)
    (matcha [types] ([[[::fn type . params] . params]]))))
```

!SLIDE

# 型推論

macroexpandを使って式をspecial formとsymbolに展開する

```clojure
(defn check [expr]
  (run* [type] (ann [] (clojure.walk/macroexpand-all expr) type)))
```

!SLIDE

# Clojureの型付けの問題

* is-a関係
* Object型

!SLIDE

# is-a関係

単純な単一化ではis-a関係を考慮できない

```clojure
user> (require '[typelogic.core :refer [check]])
nil
user> (check 0)
(java.lang.Long)
user> (check 'rationalize)
((:typelogic.core/fn java.lang.Number java.lang.Number))
user> (check '(rationalize 0))
()
```

!SLIDE

# 制約論理プログラミング

```clojure
(defna app [params args]
  ([[] []])
  ([[param . params'] [arg . args']]
     (project [param] (predc arg #(isa? % param)))
     (app params' args')))

(defn ann-app [ctx exprs type]
  (fresh [types]
    (ann-list ctx exprs types)
    (matcha [types] ([[[::fn type . params] . args]] (app params args)))))
```

is-aを制約として表現

```clojure
user> (check 'next)
(((:typelogic.core/fn _0 _1) :- (typelogic.core/isa _1 java.lang.Object) (typelogic.core/isa _0 clojure.lang.ISeq)))
```

!SLIDE

# Object型の問題

[core.clj](https://gist.github.com/halcat0x15a/8078813)

!SLIDE

# 課題

* 型付け規則が未完成
* エラーメッセージ
* etc...

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

# 論理プログラミングによる推論規則の記述

```clojure
```

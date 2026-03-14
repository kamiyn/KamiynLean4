# LeanBook

ゼロから始めるLean言語入門 ― 手を動かして学ぶ形式数学ライブラリ開発
https://www.lambdanote.com/collections/lean/products/leanbook

手習いの記録

このリポジトリには コードしかないので学習のためには本を買いましょう

# Mathlib の導入

[Using mathlib4 as a dependency](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)

ここでは lakefile.toml を使っていないため、lakefile.lean 方式で導入する。

``` lean
-- master ブランチを参照する方法
require "leanprover-community" / "mathlib"
```

バージョン固定 (git的にはタグで管理されているもの https://github.com/leanprover-community/mathlib4/releases/tag/v4.22.0) を参照
ここではこちらを指定している。

``` lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.22.0"
```

## ライブラリの取得

[Using mathlib4 as a dependency#Getting started](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency#getting-started) によれば

``` sh
lake exe cache get
```

である。

[Using mathlib4 as a dependency#Updating mathlib4](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency#updating-mathlib4) には以下のように書かれている。

``` sh
curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
lake update
```

ここには curl による lean 自体のバージョンを更新する操作を含んでおり、
main ブランチを参照する場合に lean 自体のバージョン更新が必要であると想像される。

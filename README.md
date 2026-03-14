# LeanBook

ゼロから始めるLean言語入門 ― 手を動かして学ぶ形式数学ライブラリ開発
https://www.lambdanote.com/collections/lean/products/leanbook

手習いの記録

このリポジトリには コードしかないので学習のためには本を買いましょう

# Mathlib の導入

バージョン固定 (git的にはタグで管理されているもの https://github.com/leanprover-community/mathlib4/releases/tag/v4.22.0) を指定。

``` lean
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.22.0"
```

## ライブラリの取得

``` sh
lake update mathlib # lake-manifest.json の更新を含む
lake exe cache get # Mathlib のビルド済みバイナリをダウンロード
```

## 公式ドキュメントとの違い

[Using mathlib4 as a dependency](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency)

によれば lakefile.toml を使っていないため、lakefile.lean 方式で導入する。

さらにバージョン固定されない以下の指定方法が公式ドキュメントにある。

``` sh
# Lean4 自体を更新する
# mathlib の master ブランチを参照 するにあたって lean-toolchain を更新 (すなわち Lean4 本体のバージョン更新) が必要と思われる
curl https://raw.githubusercontent.com/leanprover-community/mathlib4/master/lean-toolchain -o lean-toolchain
```

``` lean
require "leanprover-community" / "mathlib"
```

lakefile.lean 編集後の操作について、
[Using mathlib4 as a dependency#Getting started](https://github.com/leanprover-community/mathlib4/wiki/Using-mathlib4-as-a-dependency#getting-started) によれば

``` sh
lake exe cache get
```

だけが記述されているが、
(lake update をせずに) 実際に実行すると以下のエラーとなり、
lake-manifest.json の更新が必要であることがわかる。

```
> lake exe cache get
error: missing manifest; use `lake update` to generate one
```

本では lake update mathlib を実行しているが、第8章開始時点で依存ライブラリが mathlib しかないため、lake update mathlib と lake update の違いはないと思われる。

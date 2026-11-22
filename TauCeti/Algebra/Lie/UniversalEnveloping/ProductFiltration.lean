/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.UniversalEnveloping.PBW.Functoriality
public import TauCeti.Algebra.Lie.UniversalEnveloping.ProductCenter
public import TauCeti.LinearAlgebra.TensorProduct.Filtration.Basic

/-!
# The PBW filtration of a product with an abelian factor

Let `Z` be an abelian Lie algebra and `S` any Lie algebra over a commutative ring `R`. The
comparison `productEnveloping : U(Z × S) ≃ Sym(Z) ⊗ U(S)` matches the PBW filtration of
`U(Z × S)` with the total tensor filtration of the degree filtration of `Sym(Z)` (the word
filtration of `SymmetricAlgebra.ι`) and the PBW filtration of `U(S)`: an element of `U(Z × S)`
has PBW degree at most `n` exactly when its image is a sum of pure tensors `a ⊗ u` with
`deg a + deg u ≤ n`.

The forward direction holds because a canonical generator `(z, s)` goes to `z ⊗ 1 + 1 ⊗ s`, of
total degree one, and the total tensor filtration is multiplicative. The inverse direction holds
because the inverse sends `a ⊗ u` to the product of the images of `a` and `u` under the two factor
inclusions, which preserve PBW degree, and the abelian comparison `Sym(Z) ≃ U(Z)` matches the two
degree filtrations. No finiteness or characteristic hypothesis is used.

## Main results

* `TauCeti.UniversalEnvelopingAlgebra.productEnveloping_mem_tensorFiltration_iff`: the forward
  compatibility, as an equivalence of memberships.
* `TauCeti.UniversalEnvelopingAlgebra.productEnveloping_symm_mem_pbwFiltration_iff`: the inverse
  compatibility.
* `TauCeti.UniversalEnvelopingAlgebra.map_productEnveloping_pbwFiltration`: the image of each PBW
  filtration step is the corresponding total tensor filtration step.
* `TauCeti.UniversalEnvelopingAlgebra.productEnvelopingFiltration`: the induced linear
  equivalences between the filtration steps.
-/

public section

open scoped TensorProduct

namespace TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable (R : Type u) [CommRing R]
variable (Z : Type v) [LieRing Z] [LieAlgebra R Z] [IsLieAbelian Z]
variable (S : Type w) [LieRing S] [LieAlgebra R S]

local notation "US" => _root_.UniversalEnvelopingAlgebra R S
local notation "UP" => _root_.UniversalEnvelopingAlgebra R (Z × S)
local notation "SZ" => SymmetricAlgebra R Z

/-- The total tensor filtration on `Sym(Z) ⊗ U(S)` built from the degree filtration of `Sym(Z)`
and the PBW filtration of `U(S)`. -/
abbrev productFiltration (n : ℕ) : Submodule R (SZ ⊗[R] US) :=
  tensorFiltration (TauCeti.Algebra.wordFiltration (SymmetricAlgebra.ι R Z))
    (pbwFiltration R S) n

/-- The image of a canonical generator has total degree one. -/
theorem productEnveloping_ι_mem_productFiltration (x : Z × S) :
    productEnveloping R Z S (_root_.UniversalEnvelopingAlgebra.ι R x) ∈
      productFiltration R Z S 1 := by
  rw [productEnveloping_ι]
  exact add_mem
    (tmul_mem_tensorFiltration (i := 1) (j := 0) le_rfl
      (TauCeti.Algebra.apply_mem_wordFiltration_one _ _) (one_mem_pbwFiltration R S 0))
    (tmul_mem_tensorFiltration (i := 0) (j := 1) le_rfl
      (TauCeti.Algebra.one_mem_wordFiltration _ 0) (ι_mem_pbwFiltration_one R S _))

/-- The image of a word of canonical generators has total degree at most its length. -/
theorem productEnveloping_prod_map_ι_mem_productFiltration (l : List (Z × S)) :
    productEnveloping R Z S (l.map ⇑(_root_.UniversalEnvelopingAlgebra.ι R)).prod ∈
      productFiltration R Z S l.length := by
  induction l with
  | nil =>
    rw [List.map_nil, List.prod_nil, map_one]
    exact one_mem_tensorFiltration (TauCeti.Algebra.one_mem_wordFiltration _ 0)
      (one_mem_pbwFiltration R S 0) 0
  | cons x l ih =>
    rw [List.map_cons, List.prod_cons, map_mul, List.length_cons, add_comm]
    exact mul_mem_tensorFiltration (fun i j => (TauCeti.Algebra.wordFiltration_mul _ i j).le)
      (fun i j => (pbwFiltration_mul R S i j).le)
      (productEnveloping_ι_mem_productFiltration R Z S x) ih

/-- The inverse of `productEnveloping` sends total degree `n` into PBW degree `n`. -/
theorem productFiltration_le_comap_symm (n : ℕ) :
    productFiltration R Z S n ≤
      (pbwFiltration R (Z × S) n).comap (productEnveloping R Z S).symm.toLinearMap := by
  refine tensorFiltration_le_iff.mpr fun i j hij a ha s hs => ?_
  rw [Submodule.mem_comap, AlgEquiv.toLinearMap_apply, productEnveloping_symm_tmul]
  have ha' : symmetricAlgebraEquiv R Z a ∈ pbwFiltration R Z i := by
    rwa [← symmetricAlgebraEquiv_symm_mem_wordFiltration_iff, AlgEquiv.symm_apply_apply]
  exact pbwFiltration_mono R (Z × S) hij <| (pbwFiltration_mul R (Z × S) i j).le <|
    Submodule.mul_mem_mul (map_mem_pbwFiltration R _ ha') (map_mem_pbwFiltration R _ hs)

/-- **`productEnveloping` is filtered**: an element of `U(Z × S)` has PBW degree at most `n`
exactly when its image in `Sym(Z) ⊗ U(S)` has total tensor degree at most `n`. -/
@[simp]
theorem productEnveloping_mem_tensorFiltration_iff {n : ℕ} {x : UP} :
    productEnveloping R Z S x ∈ productFiltration R Z S n ↔ x ∈ pbwFiltration R (Z × S) n := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · simpa using productFiltration_le_comap_symm R Z S n hx
  · refine (pbwFiltration_le_iff R (Z × S)
      (p := (productFiltration R Z S n).comap (productEnveloping R Z S).toLinearMap)).mpr
      (fun l hl => ?_) hx
    exact tensorFiltration_mono _ _ hl (productEnveloping_prod_map_ι_mem_productFiltration R Z S l)

/-- **The inverse of `productEnveloping` is filtered**: a tensor has total degree at most `n`
exactly when its image in `U(Z × S)` has PBW degree at most `n`. -/
@[simp]
theorem productEnveloping_symm_mem_pbwFiltration_iff {n : ℕ} {t : SZ ⊗[R] US} :
    (productEnveloping R Z S).symm t ∈ pbwFiltration R (Z × S) n ↔
      t ∈ productFiltration R Z S n := by
  rw [← productEnveloping_mem_tensorFiltration_iff, AlgEquiv.apply_symm_apply]

/-- `productEnveloping` maps each PBW filtration step onto the corresponding total tensor
filtration step. -/
theorem map_productEnveloping_pbwFiltration (n : ℕ) :
    (pbwFiltration R (Z × S) n).map (productEnveloping R Z S).toLinearMap =
      productFiltration R Z S n := by
  ext t
  rw [← AlgEquiv.toLinearEquiv_toLinearMap, Submodule.mem_map_equiv,
    AlgEquiv.coe_symm_toLinearEquiv, productEnveloping_symm_mem_pbwFiltration_iff]

/-- The inverse of `productEnveloping` maps each total tensor filtration step onto the
corresponding PBW filtration step. -/
theorem map_productEnveloping_symm_productFiltration (n : ℕ) :
    (productFiltration R Z S n).map (productEnveloping R Z S).symm.toLinearMap =
      pbwFiltration R (Z × S) n := by
  ext x
  rw [← AlgEquiv.toLinearEquiv_toLinearMap, Submodule.mem_map_equiv,
    AlgEquiv.coe_symm_toLinearEquiv, AlgEquiv.symm_symm,
    productEnveloping_mem_tensorFiltration_iff]

/-- The linear equivalence between PBW filtration step `n` of `U(Z × S)` and total tensor
filtration step `n` of `Sym(Z) ⊗ U(S)` induced by `productEnveloping`. -/
noncomputable def productEnvelopingFiltration (n : ℕ) :
    pbwFiltration R (Z × S) n ≃ₗ[R] productFiltration R Z S n :=
  (productEnveloping R Z S).toLinearEquiv.ofSubmodules _ _
    (map_productEnveloping_pbwFiltration R Z S n)

/-- `productEnvelopingFiltration` acts by `productEnveloping`. -/
@[simp]
theorem coe_productEnvelopingFiltration_apply (n : ℕ) (x : pbwFiltration R (Z × S) n) :
    (productEnvelopingFiltration R Z S n x : SZ ⊗[R] US) = productEnveloping R Z S x := by
  rw [productEnvelopingFiltration, LinearEquiv.ofSubmodules_apply, AlgEquiv.coe_toLinearEquiv]

/-- The inverse of `productEnvelopingFiltration` acts by the inverse of `productEnveloping`. -/
@[simp]
theorem coe_productEnvelopingFiltration_symm_apply (n : ℕ) (t : productFiltration R Z S n) :
    ((productEnvelopingFiltration R Z S n).symm t : UP) = (productEnveloping R Z S).symm t := by
  rw [productEnvelopingFiltration, LinearEquiv.ofSubmodules_symm_apply,
    AlgEquiv.coe_symm_toLinearEquiv]

end TauCeti.UniversalEnvelopingAlgebra

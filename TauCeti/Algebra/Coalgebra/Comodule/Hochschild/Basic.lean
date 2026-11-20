/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.RingTheory.Bialgebra.Basic
public import TauCeti.Algebra.Coalgebra.Comodule.Cofree.Basic

/-!
# Hochschild cochains of a comodule

Let `H` be a bialgebra over a commutative ring `R` and `M` a right `H`-comodule. The module
of Hochschild `n`-cochains is `M ⊗ H ⊗ ⋯ ⊗ H` with `n` factors `H`. For the coordinate ring
of an affine group scheme `G` these are the functions on `Gⁿ` with values in `M`. They are
the terms of the Hochschild complex of `M`, which is constructed from the material of this
file in `TauCeti.Algebra.Coalgebra.Comodule.Hochschild.Complex`.

This file constructs the cochain modules together with their cofaces and codegeneracies and
proves the cosimplicial identities. There are `n + 2` cofaces out of degree `n`: the first
applies the coaction of `M`, the next `n` apply the comultiplication to one of the factors
`H`, and the last appends the unit of `H`. The `n + 1` codegeneracies into degree `n` apply
the counit to one of the factors `H`. No flatness or finiteness is assumed, and `H` need be
neither commutative nor a Hopf algebra; the codegeneracies and the identity between them use
only the coalgebra structure of `H`.

The cochain modules are built by recursion on the degree, adding one factor `H` on the right
at each step, so the degree `n + 1` cochains are literally a tensor product with `H`. In
these terms the cofaces of degree `n + 1` are the cofaces of degree `n` tensored with `H`,
followed by the cofree coaction on the last factor and the map appending the unit.

## Main declarations

* `TauCeti.Comodule.hochschildCochains`: the module of Hochschild `n`-cochains.
* `TauCeti.Comodule.hochschildCoface`: the cofaces.
* `TauCeti.Comodule.hochschildCodegeneracy`: the codegeneracies.
* `TauCeti.Comodule.hochschildCoface_comp_hochschildCoface`,
  `TauCeti.Comodule.hochschildCodegeneracy_comp_hochschildCoface_of_le`,
  `TauCeti.Comodule.hochschildCodegeneracy_comp_hochschildCoface_castSucc`,
  `TauCeti.Comodule.hochschildCodegeneracy_comp_hochschildCoface_succ`,
  `TauCeti.Comodule.hochschildCodegeneracy_comp_hochschildCoface_of_gt` and
  `TauCeti.Comodule.hochschildCodegeneracy_comp_hochschildCodegeneracy`: the cosimplicial
  identities.

## References

* J. C. Jantzen, *Representations of Algebraic Groups*, Part I, §§4.14–4.16.
-/

public section

open scoped TensorProduct

namespace TauCeti.Comodule

universe u v w

variable (R : Type u) (H : Type v) (M : Type (max v w))
variable [CommRing R] [AddCommGroup M] [Module R M]

section Cochains

variable [AddCommMonoid H] [Module R H]

/-- The module `M ⊗ H ⊗ ⋯ ⊗ H` of Hochschild `n`-cochains of `M`, with `n` factors `H`,
defined by adding one factor on the right at each step. -/
-- Exposed and reducible so that the degree `n + 1` cochains unfold to a tensor product
-- with `H` in the types of the cofaces and codegeneracies.
@[expose, reducible] noncomputable def hochschildCochains : ℕ → ModuleCat.{max v w} R
  | 0 => ModuleCat.of R M
  | n + 1 => ModuleCat.of R (hochschildCochains n ⊗[R] H)

/-- The Hochschild cochains of degree zero are the coefficient module. -/
theorem hochschildCochains_zero : hochschildCochains R H M 0 = ModuleCat.of R M :=
  (rfl)

/-- The Hochschild cochains of degree `n + 1` are those of degree `n` tensored with `H`. -/
theorem hochschildCochains_succ (n : ℕ) :
    hochschildCochains R H M (n + 1) = ModuleCat.of R (hochschildCochains R H M n ⊗[R] H) :=
  (rfl)

variable [Coalgebra R H]

/-- The codegeneracies of the Hochschild cochains: `hochschildCodegeneracy R H M n i` applies
the counit to the factor `H` in position `i + 1` of `M ⊗ H ⊗ ⋯ ⊗ H`. -/
noncomputable def hochschildCodegeneracy :
    ∀ n, Fin (n + 1) → (hochschildCochains R H M (n + 1) →ₗ[R] hochschildCochains R H M n)
  | 0, _ => (TensorProduct.rid R M).toLinearMap ∘ₗ Coalgebra.counit.lTensor M
  | n + 1, i => Fin.lastCases
      ((TensorProduct.rid R (hochschildCochains R H M (n + 1))).toLinearMap ∘ₗ
        Coalgebra.counit.lTensor (hochschildCochains R H M (n + 1)))
      (fun j ↦ (hochschildCodegeneracy n j).rTensor H) i

/-- The last codegeneracy applies the counit to the last factor `H`. -/
theorem hochschildCodegeneracy_last (n : ℕ) :
    hochschildCodegeneracy R H M n (Fin.last n) =
      (TensorProduct.rid R (hochschildCochains R H M n)).toLinearMap ∘ₗ
        Coalgebra.counit.lTensor (hochschildCochains R H M n) := by
  cases n
  · rfl
  · exact Fin.lastCases_last

/-- The last codegeneracy sends `x ⊗ h` to `ε(h) • x`. -/
@[simp]
theorem hochschildCodegeneracy_last_tmul (n : ℕ) (x : hochschildCochains R H M n) (h : H) :
    hochschildCodegeneracy R H M n (Fin.last n) (x ⊗ₜ[R] h) =
      Coalgebra.counit (R := R) h • x := by
  rw [hochschildCodegeneracy_last, LinearMap.comp_apply, LinearMap.lTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.rid_tmul]

/-- The codegeneracies before the last are the codegeneracies one degree lower, tensored
with `H`. -/
theorem hochschildCodegeneracy_succ_castSucc (n : ℕ) (j : Fin (n + 1)) :
    hochschildCodegeneracy R H M (n + 1) j.castSucc =
      (hochschildCodegeneracy R H M n j).rTensor H :=
  Fin.lastCases_castSucc ..

/-- The last codegeneracy is natural: it commutes with a linear map of cochains tensored
with `H`. -/
theorem hochschildCodegeneracy_last_comp_rTensor {m n : ℕ}
    (f : hochschildCochains R H M m →ₗ[R] hochschildCochains R H M n) :
    hochschildCodegeneracy R H M n (Fin.last n) ∘ₗ f.rTensor H =
      f ∘ₗ hochschildCodegeneracy R H M m (Fin.last m) := by
  rw [hochschildCodegeneracy_last, hochschildCodegeneracy_last, LinearMap.comp_assoc]
  exact rid_comp_lTensor_counit_comp_rTensor f

/-- The last codegeneracy commutes with the earlier codegeneracies. -/
private theorem hochschildCodegeneracy_last_comp (n : ℕ) (i : Fin (n + 1)) :
    hochschildCodegeneracy R H M n (Fin.last n) ∘ₗ
        hochschildCodegeneracy R H M (n + 1) i.castSucc =
      hochschildCodegeneracy R H M n i ∘ₗ
        hochschildCodegeneracy R H M (n + 1) (Fin.last (n + 1)) := by
  rw [hochschildCodegeneracy_succ_castSucc]
  exact hochschildCodegeneracy_last_comp_rTensor R H M _

/-- The cosimplicial identity for two codegeneracies: they commute after shifting the later
index. -/
theorem hochschildCodegeneracy_comp_hochschildCodegeneracy {n : ℕ} {i j : Fin (n + 1)}
    (h : i ≤ j) :
    hochschildCodegeneracy R H M n j ∘ₗ hochschildCodegeneracy R H M (n + 1) i.castSucc =
      hochschildCodegeneracy R H M n i ∘ₗ hochschildCodegeneracy R H M (n + 1) j.succ := by
  induction n with
  | zero =>
    induction j using Fin.lastCases with
    | last => exact hochschildCodegeneracy_last_comp R H M 0 i
    | cast j => exact j.elim0
  | succ n ih =>
    induction j using Fin.lastCases with
    | last => exact hochschildCodegeneracy_last_comp R H M (n + 1) i
    | cast j =>
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (h.trans_lt (Fin.castSucc_lt_last j)).ne
      rw [Fin.succ_castSucc, hochschildCodegeneracy_succ_castSucc R H M n j,
        hochschildCodegeneracy_succ_castSucc R H M n i,
        hochschildCodegeneracy_succ_castSucc R H M (n + 1) i.castSucc,
        hochschildCodegeneracy_succ_castSucc R H M (n + 1) j.succ, ← LinearMap.rTensor_comp,
        ← LinearMap.rTensor_comp, ih (Fin.castSucc_le_castSucc_iff.mp h)]

end Cochains

variable [Semiring H] [Bialgebra R H] [Comodule R H M]

/-- The cofaces of the Hochschild cochains. Out of degree `n`, the coface `0` applies the
coaction of `M`, the coface `i` with `1 ≤ i ≤ n` applies the comultiplication to the factor
`H` in position `i`, and the coface `n + 1` appends the unit of `H`. -/
noncomputable def hochschildCoface :
    ∀ n, Fin (n + 2) → (hochschildCochains R H M n →ₗ[R] hochschildCochains R H M (n + 1))
  | 0, i => Fin.lastCases ((TensorProduct.mk R M H).flip 1)
      (fun _ ↦ coact (R := R) (C := H) (M := M)) i
  | n + 1, i => Fin.lastCases ((TensorProduct.mk R (hochschildCochains R H M (n + 1)) H).flip 1)
      (Fin.lastCases (cofreeCoact R H (hochschildCochains R H M n))
        fun j ↦ (hochschildCoface n j.castSucc).rTensor H) i

/-- The last coface appends the unit of `H`. -/
theorem hochschildCoface_last (n : ℕ) :
    hochschildCoface R H M n (Fin.last (n + 1)) =
      (TensorProduct.mk R (hochschildCochains R H M n) H).flip 1 := by
  cases n <;> exact Fin.lastCases_last

/-- The last coface sends a cochain `x` to `x ⊗ 1`. -/
@[simp]
theorem hochschildCoface_last_apply (n : ℕ) (x : hochschildCochains R H M n) :
    hochschildCoface R H M n (Fin.last (n + 1)) x = x ⊗ₜ[R] (1 : H) := by
  rw [hochschildCoface_last, LinearMap.flip_apply, TensorProduct.mk_apply]

/-- The coface out of degree zero other than the last is the coaction of `M`. -/
theorem hochschildCoface_zero_castSucc (i : Fin 1) :
    hochschildCoface R H M 0 i.castSucc = coact (R := R) (C := H) (M := M) :=
  Fin.lastCases_castSucc ..

/-- The second to last coface out of a positive degree applies the comultiplication to the
last factor `H`: it is the cofree coaction. -/
theorem hochschildCoface_succ_castSucc_last (n : ℕ) :
    hochschildCoface R H M (n + 1) (Fin.last (n + 1)).castSucc =
      cofreeCoact R H (hochschildCochains R H M n) :=
  (Fin.lastCases_castSucc ..).trans Fin.lastCases_last

/-- The cofaces out of a positive degree before the last two are the cofaces one degree
lower, tensored with `H`. -/
theorem hochschildCoface_succ_castSucc_castSucc (n : ℕ) (j : Fin (n + 1)) :
    hochschildCoface R H M (n + 1) j.castSucc.castSucc =
      (hochschildCoface R H M n j.castSucc).rTensor H :=
  (Fin.lastCases_castSucc ..).trans (Fin.lastCases_castSucc ..)

/-! ### The cosimplicial identities -/

/-- The second to last coface is coassociative: it is the coaction of a comodule structure
on the cochains. -/
private theorem cofreeCoact_comp_hochschildCoface_castSucc_last (n : ℕ) :
    cofreeCoact R H (hochschildCochains R H M n) ∘ₗ
        hochschildCoface R H M n (Fin.last n).castSucc =
      (hochschildCoface R H M n (Fin.last n).castSucc).rTensor H ∘ₗ
        hochschildCoface R H M n (Fin.last n).castSucc := by
  cases n with
  | zero =>
    rw [hochschildCoface_zero_castSucc, cofreeCoact_def, LinearMap.comp_assoc,
      coact_coassoc_symm]
  | succ n =>
    -- The coaction of the cofree comodule is `cofreeCoact` by definition, so this is its
    -- coassociativity.
    let := cofree R H (hochschildCochains R H M n)
    rw [hochschildCoface_succ_castSucc_last, cofreeCoact_def, LinearMap.comp_assoc]
    exact coact_coassoc_symm (R := R) (C := H) (M := hochschildCochains R H M n ⊗[R] H)

/-- The last coface commutes with the earlier cofaces. -/
private theorem hochschildCoface_last_comp (n : ℕ) (i : Fin (n + 2)) :
    hochschildCoface R H M (n + 1) (Fin.last (n + 2)) ∘ₗ hochschildCoface R H M n i =
      hochschildCoface R H M (n + 1) i.castSucc ∘ₗ
        hochschildCoface R H M n (Fin.last (n + 1)) := by
  rw [hochschildCoface_last, hochschildCoface_last]
  induction i using Fin.lastCases with
  | last =>
    rw [hochschildCoface_succ_castSucc_last, hochschildCoface_last]
    ext x
    simp [Algebra.TensorProduct.one_def]
  | cast i =>
    rw [hochschildCoface_succ_castSucc_castSucc]
    ext x
    simp

/-- The second to last coface commutes with the earlier cofaces. -/
private theorem hochschildCoface_castSucc_last_comp (n : ℕ) (i : Fin (n + 1)) :
    hochschildCoface R H M (n + 1) (Fin.last (n + 1)).castSucc ∘ₗ
        hochschildCoface R H M n i.castSucc =
      hochschildCoface R H M (n + 1) i.castSucc.castSucc ∘ₗ
        hochschildCoface R H M n (Fin.last n).castSucc := by
  rw [hochschildCoface_succ_castSucc_last, hochschildCoface_succ_castSucc_castSucc]
  induction i using Fin.lastCases with
  | last => exact cofreeCoact_comp_hochschildCoface_castSucc_last R H M n
  | cast i =>
    cases n with
    | zero => exact i.elim0
    | succ n =>
      rw [hochschildCoface_succ_castSucc_castSucc, hochschildCoface_succ_castSucc_last]
      exact cofreeCoact_comp_rTensor _

/-- The first cosimplicial identity for the cofaces before the last. -/
private theorem hochschildCoface_castSucc_comp_hochschildCoface_castSucc {n : ℕ}
    {i j : Fin (n + 1)} (h : i ≤ j) :
    hochschildCoface R H M (n + 1) j.succ.castSucc ∘ₗ hochschildCoface R H M n i.castSucc =
      hochschildCoface R H M (n + 1) i.castSucc.castSucc ∘ₗ
        hochschildCoface R H M n j.castSucc := by
  induction n with
  | zero =>
    induction j using Fin.lastCases with
    | last => exact hochschildCoface_castSucc_last_comp R H M 0 i
    | cast j => exact j.elim0
  | succ n ih =>
    induction j using Fin.lastCases with
    | last => exact hochschildCoface_castSucc_last_comp R H M (n + 1) i
    | cast j =>
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (h.trans_lt (Fin.castSucc_lt_last j)).ne
      rw [Fin.succ_castSucc, hochschildCoface_succ_castSucc_castSucc R H M (n + 1) j.succ,
        hochschildCoface_succ_castSucc_castSucc R H M n i,
        hochschildCoface_succ_castSucc_castSucc R H M (n + 1) i.castSucc,
        hochschildCoface_succ_castSucc_castSucc R H M n j, ← LinearMap.rTensor_comp,
        ← LinearMap.rTensor_comp, ih (Fin.castSucc_le_castSucc_iff.mp h)]

/-- The first cosimplicial identity: two cofaces commute after shifting the later index. -/
theorem hochschildCoface_comp_hochschildCoface {n : ℕ} {i j : Fin (n + 2)} (h : i ≤ j) :
    hochschildCoface R H M (n + 1) j.succ ∘ₗ hochschildCoface R H M n i =
      hochschildCoface R H M (n + 1) i.castSucc ∘ₗ hochschildCoface R H M n j := by
  induction j using Fin.lastCases with
  | last => exact hochschildCoface_last_comp R H M n i
  | cast j =>
    obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (h.trans_lt (Fin.castSucc_lt_last j)).ne
    rw [Fin.succ_castSucc]
    exact hochschildCoface_castSucc_comp_hochschildCoface_castSucc R H M
      (Fin.castSucc_le_castSucc_iff.mp h)

/-- A codegeneracy cancels the coface with the same index. -/
theorem hochschildCodegeneracy_comp_hochschildCoface_castSucc {n : ℕ} (i : Fin (n + 1)) :
    hochschildCodegeneracy R H M n i ∘ₗ hochschildCoface R H M n i.castSucc =
      LinearMap.id := by
  induction n with
  | zero =>
    induction i using Fin.lastCases with
    | last =>
      rw [hochschildCodegeneracy_last, hochschildCoface_zero_castSucc]
      exact LinearMap.ext rid_lTensor_counit_coact
    | cast i => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last =>
      -- The coaction of the cofree comodule is `cofreeCoact` by definition, so this is its
      -- counit law.
      let := cofree R H (hochschildCochains R H M n)
      rw [hochschildCodegeneracy_last, hochschildCoface_succ_castSucc_last]
      exact LinearMap.ext (rid_lTensor_counit_coact (R := R) (C := H)
        (M := hochschildCochains R H M n ⊗[R] H))
    | cast i =>
      rw [hochschildCodegeneracy_succ_castSucc, hochschildCoface_succ_castSucc_castSucc,
        ← LinearMap.rTensor_comp, ih, LinearMap.rTensor_id]

/-- The last codegeneracy cancels the last coface. -/
private theorem hochschildCodegeneracy_last_comp_hochschildCoface_last (n : ℕ) :
    hochschildCodegeneracy R H M n (Fin.last n) ∘ₗ
        hochschildCoface R H M n (Fin.last (n + 1)) =
      LinearMap.id := by
  rw [hochschildCodegeneracy_last, hochschildCoface_last]
  ext x
  simp

/-- A codegeneracy cancels the coface with the next index. -/
theorem hochschildCodegeneracy_comp_hochschildCoface_succ {n : ℕ} (i : Fin (n + 1)) :
    hochschildCodegeneracy R H M n i ∘ₗ hochschildCoface R H M n i.succ = LinearMap.id := by
  induction n with
  | zero =>
    induction i using Fin.lastCases with
    | last => exact hochschildCodegeneracy_last_comp_hochschildCoface_last R H M 0
    | cast i => exact i.elim0
  | succ n ih =>
    induction i using Fin.lastCases with
    | last => exact hochschildCodegeneracy_last_comp_hochschildCoface_last R H M (n + 1)
    | cast i =>
      rw [Fin.succ_castSucc, hochschildCodegeneracy_succ_castSucc]
      induction i using Fin.lastCases with
      | last =>
        rw [Fin.succ_last, hochschildCoface_succ_castSucc_last, hochschildCodegeneracy_last]
        exact rTensor_rid_comp_lTensor_counit_comp_cofreeCoact
      | cast i =>
        rw [Fin.succ_castSucc, hochschildCoface_succ_castSucc_castSucc, ← Fin.succ_castSucc,
          ← LinearMap.rTensor_comp, ih, LinearMap.rTensor_id]

/-- A codegeneracy commutes with an earlier coface, after shifting the index of the
codegeneracy. -/
theorem hochschildCodegeneracy_comp_hochschildCoface_of_le {n : ℕ} {i : Fin (n + 2)}
    {j : Fin (n + 1)} (h : i ≤ j.castSucc) :
    hochschildCodegeneracy R H M (n + 1) j.succ ∘ₗ hochschildCoface R H M (n + 1) i.castSucc =
      hochschildCoface R H M n i ∘ₗ hochschildCodegeneracy R H M n j := by
  obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (h.trans_lt (Fin.castSucc_lt_last j)).ne
  rw [Fin.castSucc_le_castSucc_iff] at h
  rw [hochschildCoface_succ_castSucc_castSucc]
  induction n with
  | zero =>
    induction j using Fin.lastCases with
    | last => exact hochschildCodegeneracy_last_comp_rTensor R H M _
    | cast j => exact j.elim0
  | succ n ih =>
    induction j using Fin.lastCases with
    | last => exact hochschildCodegeneracy_last_comp_rTensor R H M _
    | cast j =>
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr (h.trans_lt (Fin.castSucc_lt_last j)).ne
      rw [Fin.succ_castSucc, hochschildCodegeneracy_succ_castSucc R H M (n + 1) j.succ,
        hochschildCodegeneracy_succ_castSucc R H M n j,
        hochschildCoface_succ_castSucc_castSucc R H M n i, ← LinearMap.rTensor_comp,
        ← LinearMap.rTensor_comp, ih i (Fin.castSucc_le_castSucc_iff.mp h)]

/-- A codegeneracy commutes with a later coface before the last, after shifting the index of
the coface. -/
private theorem rTensor_hochschildCodegeneracy_comp_hochschildCoface_castSucc {n : ℕ}
    {i j : Fin (n + 1)} (h : j < i) :
    (hochschildCodegeneracy R H M n j).rTensor H ∘ₗ
        hochschildCoface R H M (n + 1) i.succ.castSucc =
      hochschildCoface R H M n i.castSucc ∘ₗ hochschildCodegeneracy R H M n j := by
  induction n with
  | zero =>
    induction i using Fin.lastCases with
    | last =>
      obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr h.ne
      exact j.elim0
    | cast i => exact i.elim0
  | succ n ih =>
    obtain ⟨j, rfl⟩ := Fin.exists_castSucc_eq.mpr (h.trans_le (Fin.le_last i)).ne
    induction i using Fin.lastCases with
    | last =>
      rw [Fin.succ_last, hochschildCoface_succ_castSucc_last,
        hochschildCoface_succ_castSucc_last, hochschildCodegeneracy_succ_castSucc]
      exact (cofreeCoact_comp_rTensor _).symm
    | cast i =>
      rw [Fin.succ_castSucc, hochschildCoface_succ_castSucc_castSucc R H M (n + 1) i.succ,
        hochschildCoface_succ_castSucc_castSucc R H M n i,
        hochschildCodegeneracy_succ_castSucc R H M n j, ← LinearMap.rTensor_comp,
        ← LinearMap.rTensor_comp, ih (Fin.castSucc_lt_castSucc_iff.mp h)]

/-- A codegeneracy commutes with a later coface, after shifting the index of the coface. -/
theorem hochschildCodegeneracy_comp_hochschildCoface_of_gt {n : ℕ} {i : Fin (n + 2)}
    {j : Fin (n + 1)} (h : j.castSucc < i) :
    hochschildCodegeneracy R H M (n + 1) j.castSucc ∘ₗ hochschildCoface R H M (n + 1) i.succ =
      hochschildCoface R H M n i ∘ₗ hochschildCodegeneracy R H M n j := by
  rw [hochschildCodegeneracy_succ_castSucc]
  induction i using Fin.lastCases with
  | last =>
    rw [Fin.succ_last, hochschildCoface_last, hochschildCoface_last]
    ext x
    simp
  | cast i =>
    rw [Fin.succ_castSucc]
    exact rTensor_hochschildCodegeneracy_comp_hochschildCoface_castSucc R H M
      (Fin.castSucc_lt_castSucc_iff.mp h)

end TauCeti.Comodule

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.LocalCohomology.DegreeZero
public import TauCeti.RingTheory.CohenMacaulay.Basic
import TauCeti.Algebra.Homology.LocalCohomology.Basic
import TauCeti.Algebra.Module.Torsion.PrimaryComponent
import TauCeti.RingTheory.Depth.LocalCohomology

/-!
# The product of the annihilators of the local cohomology modules

For an ideal `J` of a commutative ring `R`, an `R`-module `M` and a natural number `d`, this file
defines the ideal
`a_J(M, d) = ∏_{0 ≤ j < d} Ann_R H^j_J(M)`,
the product of the annihilators of the local cohomology modules `H^j_J(M)` in the degrees below
`d`. It is a product of ideals, not their intersection, and the cutoff `d` is an explicit natural
number.

For a nonzero finite module `M` over a Noetherian local ring `(R, 𝔪)` with support of dimension
`d`, the ideal `a(M) = a_𝔪(M, d)` is the unit ideal when `M` is Cohen–Macaulay, since then
`H^j_𝔪(M)` vanishes below the depth, which equals `d`. Kawasaki's
construction of Cohen–Macaulay blowing-ups requires the successive entries of a parameter sequence
to lie in `a(-)` of the preceding quotients, and Schenzel's bound says that `a(M)` kills the
torsion created by dividing by part of a system of parameters.

## Main definitions

* `localCohomology.annihilatorProduct J M d`: the ideal `∏_{j < d} Ann_R H^j_J(M)`.

## Main results

* `localCohomology.annihilatorProduct_zero` and `localCohomology.annihilatorProduct_succ`: the
  empty product is `R`, and `a_J(M, d + 1) = a_J(M, d) · Ann_R H^d_J(M)`.
* `localCohomology.annihilatorProduct_le_annihilator`: `a_J(M, d)` lies in `Ann_R H^j_J(M)` for
  every `j < d`.
* `localCohomology.annihilatorProduct_eq_top_iff`: `a_J(M, d) = R` if and only if `H^j_J(M) = 0`
  for every `j < d`.
* `localCohomology.annihilatorProduct_eq_top_of_subsingleton`: `a_J(0, d) = R`.
* `localCohomology.annihilatorProduct_eq_top_of_le_depth`: `a_J(M, d) = R` when `d` is at most the
  `J`-depth of a finite module `M` over a Noetherian ring.
* `LinearEquiv.annihilatorProduct_eq`: `a_J(M, d)` is invariant under linear equivalence.
* `localCohomology.annihilator_obj_zero` and `localCohomology.annihilatorProduct_one`:
  `a_J(M, 1) = Ann_R H^0_J(M)` is the annihilator of the `J`-power torsion of `M`; by
  `localCohomology.annihilator_obj_zero_of_pow_le` it is `Ann_R M` when a power of `J` kills `M`.
* `Module.IsCohenMacaulay.annihilatorProduct_eq_top`: for a finite Cohen–Macaulay module over a
  Noetherian local ring whose support has dimension `d`, `a_𝔪(M, d) = R`.

## References

* K. Česnavičius, *Macaulayfication of Noetherian schemes*, Duke Math. J. 170 (2021),
  arXiv:1810.04493v2, Definition 3.1(ii), Remark 3.3 and Lemma 3.6.
* P. Schenzel, *Dualisierende Komplexe in der lokalen Algebra und Buchsbaum-Ringe*, Lecture Notes
  in Math. 907, Springer, 1982.
-/

public section

universe u

open CategoryTheory Limits

namespace localCohomology

variable {R : Type u} [CommRing R] (J : Ideal R) (M : Type u) [AddCommGroup M] [Module R M]

/-- The product `a_J(M, d) = ∏_{0 ≤ j < d} Ann_R H^j_J(M)` of the annihilators of the local
cohomology modules of `M` with support in `V(J)`, over the degrees below `d`. For a nonzero finite
module over a Noetherian local ring `(R, 𝔪)` whose support has dimension `d`, the ideal
`annihilatorProduct 𝔪 M d` is Česnavičius's `a(M)`. -/
noncomputable def annihilatorProduct (d : ℕ) : Ideal R :=
  ∏ j ∈ Finset.range d, Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M))

theorem annihilatorProduct_def (d : ℕ) :
    annihilatorProduct J M d =
      ∏ j ∈ Finset.range d, Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M)) :=
  (rfl)

/-- With cutoff `0` the product is empty, so it is the unit ideal. -/
@[simp]
theorem annihilatorProduct_zero : annihilatorProduct J M 0 = ⊤ := by
  rw [annihilatorProduct_def, Finset.prod_range_zero, Ideal.one_eq_top]

/-- Raising the cutoff from `d` to `d + 1` multiplies by the annihilator of `H^d_J(M)`. -/
theorem annihilatorProduct_succ (d : ℕ) :
    annihilatorProduct J M (d + 1) =
      annihilatorProduct J M d *
        Module.annihilator R ((localCohomology J d).obj (ModuleCat.of R M)) := by
  simp only [annihilatorProduct_def, Finset.prod_range_succ]

/-- With cutoff `1` the product is the annihilator of `H^0_J(M)`. -/
theorem annihilatorProduct_one :
    annihilatorProduct J M 1 =
      Module.annihilator R ((localCohomology J 0).obj (ModuleCat.of R M)) := by
  rw [annihilatorProduct_succ, annihilatorProduct_zero, Ideal.top_mul]

/-- The product `a_J(M, d)` lies in each of its factors `Ann_R H^j_J(M)`, `j < d`. -/
theorem annihilatorProduct_le_annihilator {d j : ℕ} (hj : j < d) :
    annihilatorProduct J M d ≤
      Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M)) :=
  Ideal.prod_le_inf.trans (Finset.inf_le (Finset.mem_range.2 hj))

/-- The product `a_J(M, d)` shrinks as the cutoff `d` grows. -/
theorem annihilatorProduct_antitone : Antitone (annihilatorProduct J M) :=
  antitone_nat_of_succ_le fun d ↦ (annihilatorProduct_succ J M d).trans_le Ideal.mul_le_left

/-- The product `a_J(M, d)` is the unit ideal if and only if `H^j_J(M) = 0` for every `j < d`. -/
theorem annihilatorProduct_eq_top_iff {d : ℕ} :
    annihilatorProduct J M d = ⊤ ↔
      ∀ j < d, IsZero ((localCohomology J j).obj (ModuleCat.of R M)) := by
  have key (j : ℕ) : IsZero ((localCohomology J j).obj (ModuleCat.of R M)) ↔
      Module.annihilator R ((localCohomology J j).obj (ModuleCat.of R M)) = ⊤ :=
    ModuleCat.isZero_iff_subsingleton.trans Module.annihilator_eq_top_iff.symm
  simp only [key]
  refine ⟨fun h j hj ↦ top_unique (h ▸ annihilatorProduct_le_annihilator J M hj), fun h ↦ ?_⟩
  rw [annihilatorProduct_def, ← Ideal.one_eq_top]
  exact Finset.prod_eq_one fun j hj ↦ (h j (Finset.mem_range.1 hj)).trans Ideal.one_eq_top.symm

/-- All local cohomology of the zero module vanishes, so `a_J(0, d)` is the unit ideal. -/
@[simp]
theorem annihilatorProduct_eq_top_of_subsingleton [Subsingleton M] (d : ℕ) :
    annihilatorProduct J M d = ⊤ :=
  (annihilatorProduct_eq_top_iff J M).2 fun j _ ↦ isZero_obj_of_subsingleton J j _

/-- If `d` is at most the `J`-depth of a finite module `M` over a Noetherian ring, then the local
cohomology modules `H^j_J(M)`, `j < d`, vanish, so `a_J(M, d)` is the unit ideal. -/
theorem annihilatorProduct_eq_top_of_le_depth [IsNoetherianRing R] [Module.Finite R M] {d : ℕ}
    (h : (d : ℕ∞) ≤ J.depth (ModuleCat.of R M)) : annihilatorProduct J M d = ⊤ :=
  (annihilatorProduct_eq_top_iff J M).2 fun _ hj ↦
    isZero_obj_of_lt_depth J _ ((Nat.cast_lt.2 hj).trans_le h)

/-- The annihilator of `H^0_J(M)` is the annihilator of the `J`-power torsion
`Ideal.primaryComponent M J` of `M`, the union of the annihilators in `M` of the powers of `J`. -/
theorem annihilator_obj_zero :
    Module.annihilator R ((localCohomology J 0).obj (ModuleCat.of R M)) =
      (J.primaryComponent M).annihilator := by
  let f := (degreeZeroToModule J (ModuleCat.of R M)).hom
  exact ((LinearEquiv.ofInjective f (degreeZeroToModule_injective J _)).trans
    (LinearEquiv.ofEq _ _ (range_hom_degreeZeroToModule J _))).annihilator_eq

/-- If some power of `J` kills `M`, then `H^0_J(M) = M`, so the annihilator of `H^0_J(M)` is
that of `M`. For example `Ann_R H^0_J(R ⧸ I) = I` whenever `Jⁿ ⊆ I`. -/
theorem annihilator_obj_zero_of_pow_le {n : ℕ} (h : J ^ n ≤ Module.annihilator R M) :
    Module.annihilator R ((localCohomology J 0).obj (ModuleCat.of R M)) =
      Module.annihilator R M := by
  rw [annihilator_obj_zero, J.primaryComponent_eq_top_of_le_annihilator h,
    Submodule.annihilator_top]

end localCohomology

namespace LinearEquiv

open localCohomology

variable {R : Type u} [CommRing R] {M N : Type u} [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N]

/-- The product `a_J(M, d)` depends on `M` only up to linear equivalence. -/
theorem annihilatorProduct_eq (e : M ≃ₗ[R] N) (J : Ideal R) (d : ℕ) :
    annihilatorProduct J M d = annihilatorProduct J N d := by
  simp only [annihilatorProduct_def]
  exact Finset.prod_congr rfl fun j _ ↦
    ((localCohomology J j).mapIso e.toModuleIso).toLinearEquiv.annihilator_eq

end LinearEquiv

namespace Module.IsCohenMacaulay

open localCohomology _root_.IsLocalRing

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] {M : Type u}
  [AddCommGroup M] [Module R M] [Module.Finite R M]

/-- For a finite Cohen–Macaulay module `M` over a Noetherian local ring `(R, 𝔪)` whose support has
dimension `d`, the local cohomology modules `H^j_𝔪(M)`, `j < d`, vanish, so `a_𝔪(M, d)` is the
unit ideal. -/
theorem annihilatorProduct_eq_top (hM : IsCohenMacaulay R M) {d : ℕ}
    (hd : supportDim R M = d) : annihilatorProduct (maximalIdeal R) M d = ⊤ := by
  cases subsingleton_or_nontrivial M
  · exact annihilatorProduct_eq_top_of_subsingleton _ M d
  -- A nonzero Cohen–Macaulay module has depth `d`.
  refine annihilatorProduct_eq_top_of_le_depth _ M (le_of_eq ?_)
  have := hM.depth_eq
  rw [hd] at this
  rw [← depth]
  exact_mod_cast this.symm

end Module.IsCohenMacaulay

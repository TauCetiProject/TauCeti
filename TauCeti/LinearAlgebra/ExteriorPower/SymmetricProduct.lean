/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.ExteriorPower
public import TauCeti.LinearAlgebra.ExteriorPower.Basic
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring
import TauCeti.Algebra.BigOperators.Finset.Pairs
import TauCeti.LinearAlgebra.ExteriorPower.Square
import TauCeti.Order.Hom.PowersetCard

/-!
# Symmetric exterior product of linear maps on the second exterior power

When `2` is invertible in a commutative ring `R`, any two linear maps `f, g : M →ₗ[R] N` induce
`exteriorPower.symmMap₂ f g : ⋀[R]^2 M →ₗ[R] ⋀[R]^2 N` given on pure wedges by
`(f ∧ g)(u ∧ v) = ⅟2 • (f u ∧ g v + g u ∧ f v)`. On the diagonal `symmMap₂ f f = map 2 f`, and
pairing an endomorphism with `id` gives half the derivation action `exteriorPower.lieMap 2`.
On finite free modules, `tr(symmMap₂ f g) = ⅟2 * (tr f · tr g - tr(f ∘ g))` and in particular
`tr(symmMap₂ f id) = ((finrank R M - 1) * ⅟2) * tr f`.

In Riemannian geometry (`Böhm–Wilking, Section 2`; cf. `Besse, Section 1.G` for the unnormalized
bilinear-form Kulkarni–Nomizu product `h ⊙ k`), this `⅟2`-normalized operator wedge product is the
operator-side counterpart of the Kulkarni–Nomizu product, expressing the scalar curvature operator
via `id ∧ id = id` and the traceless-Ricci operator via `Ric₀ ∧ id`.

## Main definitions

* `exteriorPower.symmMap₂`: `(f, g) ↦ (u ∧ v ↦ ⅟2 • (f u ∧ g v + g u ∧ f v))`.

## Main results

* `exteriorPower.symmMap₂_apply_ιMulti`, `exteriorPower.symmMap₂_comm`,
  `exteriorPower.symmMap₂_self`, `exteriorPower.symmMap₂_id_right`,
  `exteriorPower.symmMap₂_id_left`, `exteriorPower.symmMap₂_comp_symmMap₂`,
  `exteriorPower.map_comp_symmMap₂`, `exteriorPower.symmMap₂_comp_map`,
  `LinearEquiv.exteriorPower_arrowCongr_symmMap₂`, `LinearEquiv.exteriorPower_conj_symmMap₂`,
  `exteriorPower.trace_symmMap₂`, and `exteriorPower.trace_symmMap₂_id_right`.

## References

* C. Böhm and B. Wilking, *Manifolds with positive curvature operators are space forms*,
  Ann. of Math. 167 (2008), 1079–1097, Section 2.
* A. L. Besse, *Einstein Manifolds*, Springer (1987), Section 1.G.
-/

public section

namespace exteriorPower

variable {R M N : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]

private noncomputable def symmWedgeBilin (f g : M →ₗ[R] N) : M →ₗ[R] M →ₗ[R] ⋀[R]^2 N :=
  LinearMap.mk₂ R (fun u v ↦ ⅟(2 : R) • (ιMulti R 2 ![f u, g v] + ιMulti R 2 ![g u, f v]))
    (fun _ _ _ ↦ by simp only [map_add, ιMulti_two_add_left]; module)
    (fun _ _ _ ↦ by simp only [map_smul, ιMulti_two_smul_left]; module)
    (fun _ _ _ ↦ by simp only [map_add, ιMulti_two_add_right]; module)
    (fun _ _ _ ↦ by simp only [map_smul, ιMulti_two_smul_right]; module)

private theorem isAlt_symmWedgeBilin (f g : M →ₗ[R] N) : (symmWedgeBilin f g).IsAlt := fun x ↦ by
  simp [symmWedgeBilin, ιMulti_two_swap (f x) (g x)]

/-- The symmetric exterior product of two linear maps `f, g : M →ₗ[R] N` on the second exterior
power, characterized by `symmMap₂ f g (u ∧ v) = ⅟2 • (f u ∧ g v + g u ∧ f v)`. -/
noncomputable def symmMap₂ :
    (M →ₗ[R] N) →ₗ[R] (M →ₗ[R] N) →ₗ[R] (⋀[R]^2 M →ₗ[R] ⋀[R]^2 N) := by
  refine LinearMap.mk₂ R (fun f g ↦ alternatingMapLinearEquiv
    (isAlt_symmWedgeBilin f g).toAlternatingMap) ?_ ?_ ?_ ?_ <;>
  refine fun _ _ _ ↦ linearMap_ext_ιMulti_two fun _ _ ↦ ?_ <;>
  simp only [LinearMap.add_apply, LinearMap.smul_apply, symmWedgeBilin,
    alternatingMapLinearEquiv_apply_ιMulti, LinearMap.IsAlt.toAlternatingMap_apply,
    LinearMap.mk₂_apply, Matrix.cons_val_zero, Matrix.cons_val_one, ιMulti_two_add_left,
    ιMulti_two_add_right, ιMulti_two_smul_left, ιMulti_two_smul_right] <;> module

/-- On `u ∧ v`, `symmMap₂ f g` evaluates to `⅟2 • (f u ∧ g v + g u ∧ f v)`. -/
@[simp] theorem symmMap₂_apply_ιMulti (f g : M →ₗ[R] N) (u v : M) :
    symmMap₂ f g (ιMulti R 2 ![u, v]) =
      ⅟(2 : R) • (ιMulti R 2 ![f u, g v] + ιMulti R 2 ![g u, f v]) := by
  simp [symmMap₂, symmWedgeBilin]

/-- Tuple-indexed form of `symmMap₂_apply_ιMulti`. -/
theorem symmMap₂_apply_ιMulti_tuple (f g : M →ₗ[R] N) (v : Fin 2 → M) :
    symmMap₂ f g (ιMulti R 2 v) =
      ⅟(2 : R) • (ιMulti R 2 ![f (v 0), g (v 1)] + ιMulti R 2 ![g (v 0), f (v 1)]) := by
  rw [← symmMap₂_apply_ιMulti, ← FinVec.etaExpand_eq v]; rfl

/-- `symmMap₂` is symmetric in its two linear-map arguments. -/
theorem symmMap₂_comm (f g : M →ₗ[R] N) : symmMap₂ f g = symmMap₂ g f :=
  linearMap_ext_ιMulti_two fun _ _ ↦ by simp only [symmMap₂_apply_ιMulti, add_comm]

/-- On the diagonal `(f, f)`, `symmMap₂` agrees with `exteriorPower.map 2 f`. -/
@[simp] theorem symmMap₂_self (f : M →ₗ[R] N) : symmMap₂ f f = map 2 f :=
  linearMap_ext_ιMulti_two fun _ _ ↦ by simp only [symmMap₂_apply_ιMulti, map_apply_ιMulti_two,
    ← two_smul R, smul_smul, invOf_mul_self, one_smul]

/-- Pairing an endomorphism `f` with `id` gives half the derivation action `lieMap 2 f`. -/
theorem symmMap₂_id_right (f : Module.End R M) :
    symmMap₂ f LinearMap.id = ⅟(2 : R) • lieMap 2 f :=
  linearMap_ext_ιMulti_two fun _ _ ↦ by simp only [symmMap₂_apply_ιMulti, LinearMap.id_apply,
    LinearMap.smul_apply, lieMap_two_apply_ιMulti]

/-- Pairing `id` with an endomorphism `f` gives half the derivation action `lieMap 2 f`. -/
theorem symmMap₂_id_left (f : Module.End R M) :
    symmMap₂ LinearMap.id f = ⅟(2 : R) • lieMap 2 f := by rw [symmMap₂_comm, symmMap₂_id_right]

variable {P : Type*} [AddCommGroup P] [Module R P]

/-- Composition law for `symmMap₂`:
`(f₁ ∧ g₁) ∘ (f₂ ∧ g₂) = ⅟2 • ((f₁ ∘ f₂) ∧ (g₁ ∘ g₂) + (f₁ ∘ g₂) ∧ (g₁ ∘ f₂))`. -/
theorem symmMap₂_comp_symmMap₂ (f₁ g₁ : N →ₗ[R] P) (f₂ g₂ : M →ₗ[R] N) :
    (symmMap₂ f₁ g₁).comp (symmMap₂ f₂ g₂) =
      ⅟(2 : R) • (symmMap₂ (f₁.comp f₂) (g₁.comp g₂) + symmMap₂ (f₁.comp g₂) (g₁.comp f₂)) :=
  linearMap_ext_ιMulti_two fun _ _ ↦ by simp only [LinearMap.comp_apply, LinearMap.smul_apply,
    LinearMap.add_apply, symmMap₂_apply_ιMulti, map_smul, map_add]; module

/-- Naturality of `symmMap₂` under post-composition with `map 2 h`. -/
theorem map_comp_symmMap₂ (h : N →ₗ[R] P) (f g : M →ₗ[R] N) :
    (map 2 h).comp (symmMap₂ f g) = symmMap₂ (h.comp f) (h.comp g) := by
  rw [← symmMap₂_self h, symmMap₂_comp_symmMap₂, symmMap₂_comm (h.comp g) (h.comp f), ← two_smul R,
    smul_smul, invOf_mul_self, one_smul]

/-- Naturality of `symmMap₂` under pre-composition with `map 2 h`. -/
theorem symmMap₂_comp_map (f g : N →ₗ[R] P) (h : M →ₗ[R] N) :
    (symmMap₂ f g).comp (map 2 h) = symmMap₂ (f.comp h) (g.comp h) := by
  rw [← symmMap₂_self h, symmMap₂_comp_symmMap₂, ← two_smul R, smul_smul, invOf_mul_self, one_smul]

section Trace

private theorem sum_powersetCard_two_of_symm_of_diag_eq_zero
    {I G : Type*} [Fintype I] [LinearOrder I] [AddCommMonoid G]
    (F : I → I → G) (hsymm : ∀ i j, F i j = F j i) (hdiag : ∀ i, F i i = 0) :
    (∑ i, ∑ j, F i j) = 2 • ∑ s : Set.powersetCard I 2,
      F (Set.powersetCard.ofFinEmbEquiv.symm s 0) (Set.powersetCard.ofFinEmbEquiv.symm s 1) := by
  rw [TauCeti.sum_symmetric_pairs F hsymm]
  simp only [hdiag, Finset.sum_const_zero, zero_add]
  congr 1
  exact (Fintype.sum_equiv (Set.powersetCard.ofLtPair (I := I)).symm _ _ fun s ↦ by
    simp [Set.powersetCard.ofLtPair_symm_apply]).symm

private theorem toMatrix_symmMap₂_diag {I : Type*} [LinearOrder I] [Fintype I] [DecidableEq I]
    (b : Module.Basis I R M) (f g : Module.End R M) (s : Set.powersetCard I 2) :
    LinearMap.toMatrix (b.exteriorPower 2) (b.exteriorPower 2) (symmMap₂ f g) s s =
      ⅟(2 : R) *
        (LinearMap.toMatrix b b f (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm s 0) *
          LinearMap.toMatrix b b g (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm s 1) -
        LinearMap.toMatrix b b f (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm s 0) *
          LinearMap.toMatrix b b g (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm s 1) +
        LinearMap.toMatrix b b g (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm s 0) *
          LinearMap.toMatrix b b f (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm s 1) -
        LinearMap.toMatrix b b g (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm s 0) *
          LinearMap.toMatrix b b f (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm s 1)) := by
  rw [LinearMap.toMatrix_apply, basis_apply, ιMulti_family, symmMap₂_apply_ιMulti_tuple,
    map_smul, map_add, Finsupp.smul_apply, Finsupp.add_apply, basis_repr_apply,
    basis_repr_apply, ιMultiDual_apply_ιMulti, ιMultiDual_apply_ιMulti,
    Matrix.det_fin_two, Matrix.det_fin_two, smul_eq_mul]
  simp only [LinearMap.toMatrix_apply, Module.Basis.coord_apply, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Function.comp_apply]
  ring

variable [Module.Free R M] [Module.Finite R M]

/-- The trace of `symmMap₂ f g` on `⋀[R]^2 M` is `⅟2 * (tr f * tr g - tr(f ∘ₗ g))`.
Neither `f` nor `g` need be symmetric. -/
theorem trace_symmMap₂ (f g : Module.End R M) :
    LinearMap.trace R (⋀[R]^2 M) (symmMap₂ f g) =
      ⅟(2 : R) * (LinearMap.trace R M f * LinearMap.trace R M g -
        LinearMap.trace R M (f ∘ₗ g)) := by
  classical
  cases subsingleton_or_nontrivial R
  · simp [eq_iff_true_of_subsingleton]
  let I := Module.Free.ChooseBasisIndex R M
  let _ : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis R M
  let A := LinearMap.toMatrix b b f
  let C := LinearMap.toMatrix b b g
  let F (i j : I) : R := A i i * C j j - A j i * C i j + C i i * A j j - C j i * A i j
  have htr : LinearMap.trace R (⋀[R]^2 M) (symmMap₂ f g) =
      ⅟(2 : R) * ∑ s : Set.powersetCard I 2,
        F (Set.powersetCard.ofFinEmbEquiv.symm s 0)
          (Set.powersetCard.ofFinEmbEquiv.symm s 1) := by
    rw [LinearMap.trace_eq_matrix_trace R (b.exteriorPower 2) (symmMap₂ f g), Matrix.trace]
    simp_rw [Matrix.diag, toMatrix_symmMap₂_diag b f g, ← Finset.mul_sum]
    rfl
  have hsum : ∑ i : I, ∑ j : I, F i j =
      2 • ∑ s : Set.powersetCard I 2,
        F (Set.powersetCard.ofFinEmbEquiv.symm s 0)
          (Set.powersetCard.ofFinEmbEquiv.symm s 1) :=
    sum_powersetCard_two_of_symm_of_diag_eq_zero F (fun _ _ ↦ by simp only [F]; ring)
      (fun _ ↦ by simp only [F]; ring)
  have hdiag (h : Module.End R M) :
      ∑ i : I, LinearMap.toMatrix b b h i i = LinearMap.trace R M h :=
    (LinearMap.trace_eq_matrix_trace R b h).symm
  have hoff (f₁ f₂ : Module.End R M) :
      ∑ i : I, ∑ j : I, LinearMap.toMatrix b b f₁ j i * LinearMap.toMatrix b b f₂ i j =
        LinearMap.trace R M (f₁ ∘ₗ f₂) := by
    rw [LinearMap.trace_eq_matrix_trace R b (f₁ ∘ₗ f₂), LinearMap.toMatrix_comp b b b f₁ f₂,
      Matrix.trace]
    simp_rw [Matrix.diag, Matrix.mul_apply]
    exact Finset.sum_comm
  have hF : ∑ i : I, ∑ j : I, F i j =
      2 * (LinearMap.trace R M f * LinearMap.trace R M g - LinearMap.trace R M (f ∘ₗ g)) := by
    have h1 : ∑ i : I, ∑ j : I, A i i * C j j =
        LinearMap.trace R M f * LinearMap.trace R M g := by
      dsimp only [A, C]; simp_rw [← Finset.mul_sum, ← Finset.sum_mul, hdiag]
    have h2 : ∑ i : I, ∑ j : I, C i i * A j j =
        LinearMap.trace R M g * LinearMap.trace R M f := by
      dsimp only [A, C]; simp_rw [← Finset.mul_sum, ← Finset.sum_mul, hdiag]
    have h3 : ∑ i : I, ∑ j : I, C j i * A i j = LinearMap.trace R M (f ∘ₗ g) :=
      (hoff g f).trans (LinearMap.trace_comp_comm' g f).symm
    dsimp only [F, A, C]
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    dsimp only [A, C] at h1 h2 h3
    rw [h1, h2, hoff f g, h3]
    ring
  have h2 := congrArg (⅟(2 : R) * ·) (hsum.symm.trans hF)
  rw [nsmul_eq_mul, Nat.cast_ofNat, ← mul_assoc, ← mul_assoc, invOf_mul_self, one_mul,
    one_mul] at h2
  rw [htr, h2]

/-- The trace of `symmMap₂ f id` on `⋀[R]^2 M` is `((finrank R M - 1) * ⅟2) * tr f`. -/
theorem trace_symmMap₂_id_right (f : Module.End R M) :
    LinearMap.trace R (⋀[R]^2 M) (symmMap₂ f LinearMap.id) =
      ((Module.finrank R M : R) - 1) * ⅟(2 : R) * LinearMap.trace R M f := by
  rw [trace_symmMap₂, LinearMap.trace_id, LinearMap.comp_id]
  ring

end Trace

end exteriorPower

namespace LinearEquiv

variable {R M N M' N' : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

/-- Transporting `exteriorPower.symmMap₂ f g` along domain and codomain equivalences `e₁` and `e₂`
transports each factor via `e₁.arrowCongr e₂`. -/
theorem exteriorPower_arrowCongr_symmMap₂ (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (f g : M →ₗ[R] N) :
    ((e₁.exteriorPower 2).arrowCongr (e₂.exteriorPower 2)) (exteriorPower.symmMap₂ f g) =
      exteriorPower.symmMap₂ (e₁.arrowCongr e₂ f) (e₁.arrowCongr e₂ g) := by
  change (e₂.exteriorPower 2).toLinearMap ∘ₗ exteriorPower.symmMap₂ f g ∘ₗ
        (e₁.exteriorPower 2).symm.toLinearMap =
      exteriorPower.symmMap₂ (e₂.toLinearMap ∘ₗ f ∘ₗ e₁.symm.toLinearMap)
        (e₂.toLinearMap ∘ₗ g ∘ₗ e₁.symm.toLinearMap)
  simp only [LinearEquiv.exteriorPower_symm, LinearEquiv.exteriorPower_toLinearMap,
    exteriorPower.symmMap₂_comp_map, exteriorPower.map_comp_symmMap₂]

/-- Conjugating `exteriorPower.symmMap₂ f g` by `e.exteriorPower 2` conjugates each factor. -/
theorem exteriorPower_conj_symmMap₂ (e : M ≃ₗ[R] N) (f g : Module.End R M) :
    (e.exteriorPower 2).conj (exteriorPower.symmMap₂ f g) =
      exteriorPower.symmMap₂ (e.conj f) (e.conj g) :=
  exteriorPower_arrowCongr_symmMap₂ e e f g

end LinearEquiv

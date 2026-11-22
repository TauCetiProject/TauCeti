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
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.LinearAlgebra.ExteriorPower.Square
import TauCeti.Order.Hom.PowersetCard

/-!
# Symmetric exterior product of linear maps on the second exterior power

When `2` is invertible in a commutative ring `R`, any two linear maps `f, g : M →ₗ[R] N` induce
`exteriorPower.symmMap₂ f g : ⋀[R]^2 M →ₗ[R] ⋀[R]^2 N` given on pure wedges by
`(f ∧ g)(u ∧ v) = ⅟2 • (f u ∧ g v + g u ∧ f v)`. On the diagonal `symmMap₂ f f = map 2 f`, and
pairing an endomorphism with `id` gives half the derivation action `exteriorPower.lieMap 2`.
Polarizing `map 2` yields `symmMap₂ f g = ⅟2 • (map 2 (f + g) - map 2 f - map 2 g)` and the
minor formula `Module.Basis.toMatrix_exteriorPower_symmMap₂`. On finite free modules,
`tr(symmMap₂ f g) = ⅟2 * (tr f · tr g - tr(f ∘ g))` and in particular
`tr(symmMap₂ f id) = ((finrank R M - 1) * ⅟2) * tr f`.

In Riemannian geometry (`Böhm–Wilking, Section 2`; cf. `Besse, Section 1.G` for the unnormalized
bilinear-form Kulkarni–Nomizu product `h ⊙ k`), this `⅟2`-normalized operator wedge product is the
operator-side counterpart of the Kulkarni–Nomizu product, expressing the scalar curvature operator
via `id ∧ id = id` and the traceless-Ricci operator via `Ric₀ ∧ id`.

## Main definitions

* `exteriorPower.symmMap₂`: `(f, g) ↦ (u ∧ v ↦ ⅟2 • (f u ∧ g v + g u ∧ f v))`.

## Main results

* `exteriorPower.symmMap₂_apply_ιMulti`, `exteriorPower.symmMap₂_comm`,
  `exteriorPower.symmMap₂_self`, `exteriorPower.symmMap₂_eq_invOf_two_smul_map_add_sub`,
  `exteriorPower.symmMap₂_id_right`, `exteriorPower.symmMap₂_id_left`,
  `exteriorPower.symmMap₂_comp_symmMap₂`, `exteriorPower.map_comp_symmMap₂`,
  `exteriorPower.symmMap₂_comp_map`, `Module.Basis.toMatrix_exteriorPower_symmMap₂`,
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

/-- Polarization identity expressing `symmMap₂ f g` in terms of `exteriorPower.map 2`. -/
theorem symmMap₂_eq_invOf_two_smul_map_add_sub (f g : M →ₗ[R] N) :
    symmMap₂ f g = ⅟(2 : R) • (map 2 (f + g) - map 2 f - map 2 g) := by
  have h : map 2 (f + g) - map 2 f - map 2 g = (2 : R) • symmMap₂ f g := by
    rw [← symmMap₂_self (f + g), ← symmMap₂_self f, ← symmMap₂_self g]
    simp only [map_add, LinearMap.add_apply, symmMap₂_comm g f, two_smul]
    abel
  rw [h, smul_smul, invOf_mul_self, one_smul]

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

end exteriorPower

namespace Module.Basis

variable {R M N I J : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [LinearOrder I] [Fintype I] [LinearOrder J] [Finite J]

/-- Matrix entries of `exteriorPower.symmMap₂ f g` with respect to exterior-square bases. -/
theorem toMatrix_exteriorPower_symmMap₂ (b : Basis I R M) (c : Basis J R N) (f g : M →ₗ[R] N)
    (s : Set.powersetCard J 2) (t : Set.powersetCard I 2) :
    LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2) (exteriorPower.symmMap₂ f g) s t =
      ⅟(2 : R) *
        (LinearMap.toMatrix b c f (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm t 0) *
          LinearMap.toMatrix b c g (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm t 1) -
        LinearMap.toMatrix b c f (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm t 0) *
          LinearMap.toMatrix b c g (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm t 1) +
        LinearMap.toMatrix b c g (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm t 0) *
          LinearMap.toMatrix b c f (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm t 1) -
        LinearMap.toMatrix b c g (Set.powersetCard.ofFinEmbEquiv.symm s 1)
            (Set.powersetCard.ofFinEmbEquiv.symm t 0) *
          LinearMap.toMatrix b c f (Set.powersetCard.ofFinEmbEquiv.symm s 0)
            (Set.powersetCard.ofFinEmbEquiv.symm t 1)) := by
  have hmat : LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2)
      (exteriorPower.symmMap₂ f g) =
      ⅟(2 : R) • (LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2)
          (exteriorPower.map 2 (f + g)) -
        LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2) (exteriorPower.map 2 f) -
        LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2) (exteriorPower.map 2 g)) := by
    simp only [exteriorPower.symmMap₂_eq_invOf_two_smul_map_add_sub, map_smul,
      map_sub (LinearMap.toMatrix (b.exteriorPower 2) (c.exteriorPower 2))]
  rw [hmat]
  simp only [Matrix.smul_apply, Matrix.sub_apply, toMatrix_exteriorPower_map, smul_eq_mul,
    Matrix.det_fin_two, Matrix.of_apply, map_add, Matrix.add_apply]
  ring

end Module.Basis

namespace exteriorPower

section Trace

private theorem sum_diag_mul_diag {I R : Type*} [Fintype I] [CommSemiring R]
    (A C : Matrix I I R) :
    ∑ i, ∑ j, A i i * C j j = A.trace * C.trace := by
  simp_rw [← Finset.mul_sum, ← Finset.sum_mul, Matrix.trace, Matrix.diag]

private theorem sum_offDiag_mul_eq_trace_mul {I R : Type*} [Fintype I] [CommSemiring R]
    (A C : Matrix I I R) :
    ∑ i, ∑ j, A j i * C i j = (A * C).trace := by
  simp_rw [Matrix.trace, Matrix.diag, Matrix.mul_apply]
  exact Finset.sum_comm

private theorem sum_symmMinor_eq_two_mul_trace_sub {I R : Type*} [Fintype I] [CommRing R]
    (A C : Matrix I I R) :
    ∑ i, ∑ j, (A i i * C j j - A j i * C i j + C i i * A j j - C j i * A i j) =
      2 * (A.trace * C.trace - (A * C).trace) := by
  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, sum_diag_mul_diag,
    sum_offDiag_mul_eq_trace_mul, Matrix.trace_mul_comm C A]
  ring

variable {R M : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/-- The trace of `symmMap₂ f g` on `⋀[R]^2 M` is `⅟2 * (tr f * tr g - tr(f ∘ₗ g))`.
Neither `f` nor `g` need be symmetric. -/
theorem trace_symmMap₂ (f g : Module.End R M) :
    LinearMap.trace R (⋀[R]^2 M) (symmMap₂ f g) =
      ⅟(2 : R) * (LinearMap.trace R M f * LinearMap.trace R M g -
        LinearMap.trace R M (f ∘ₗ g)) := by
  cases subsingleton_or_nontrivial R
  · simp [eq_iff_true_of_subsingleton]
  let I := Module.Free.ChooseBasisIndex R M
  let _ : DecidableRel (WellOrderingRel (α := I)) := Classical.decRel _
  let _ : LinearOrder I := linearOrderOfSTO WellOrderingRel
  let b := Module.Free.chooseBasis R M
  let A := LinearMap.toMatrix b b f
  let C := LinearMap.toMatrix b b g
  let F (i j : I) : R := A i i * C j j - A j i * C i j + C i i * A j j - C j i * A i j
  have htr : LinearMap.trace R (⋀[R]^2 M) (symmMap₂ f g) =
      ⅟(2 : R) * ∑ s : Set.powersetCard I 2,
        F (Set.powersetCard.ofFinEmbEquiv.symm s 0)
          (Set.powersetCard.ofFinEmbEquiv.symm s 1) := by
    rw [LinearMap.trace_eq_matrix_trace R (b.exteriorPower 2) (symmMap₂ f g), Matrix.trace,
      Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ ↦ ?_
    have h := b.toMatrix_exteriorPower_symmMap₂ b f g s s
    dsimp only [Matrix.diag, F, A, C] at h ⊢
    simpa only [LinearMap.toMatrix_apply] using h
  have hsum : ∑ i : I, ∑ j : I, F i j =
      2 • ∑ s : Set.powersetCard I 2,
        F (Set.powersetCard.ofFinEmbEquiv.symm s 0)
          (Set.powersetCard.ofFinEmbEquiv.symm s 1) :=
    Set.powersetCard.sum_two_of_symm_of_diag_eq_zero F (fun _ _ ↦ by simp only [F]; ring)
      (fun _ ↦ by simp only [F]; ring)
  have hF : ∑ i : I, ∑ j : I, F i j =
      2 * (LinearMap.trace R M f * LinearMap.trace R M g - LinearMap.trace R M (f ∘ₗ g)) := by
    rw [LinearMap.trace_eq_matrix_trace R b f, LinearMap.trace_eq_matrix_trace R b g,
      LinearMap.trace_eq_matrix_trace R b (f ∘ₗ g), LinearMap.toMatrix_comp b b b f g]
    exact sum_symmMinor_eq_two_mul_trace_sub A C
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

private theorem arrowCongr_eq_comp {R A B A' B' : Type*} [CommRing R]
    [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B]
    [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
    (e₁ : A ≃ₗ[R] A') (e₂ : B ≃ₗ[R] B') (f : A →ₗ[R] B) :
    e₁.arrowCongr e₂ f = e₂.toLinearMap ∘ₗ f ∘ₗ e₁.symm.toLinearMap :=
  LinearMap.ext fun x ↦ e₁.arrowCongr_apply e₂ f x

variable {R M N M' N' : Type*} [CommRing R] [Invertible (2 : R)]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']

/-- Transporting `exteriorPower.symmMap₂ f g` along domain and codomain equivalences `e₁` and `e₂`
transports each factor via `e₁.arrowCongr e₂`. -/
theorem exteriorPower_arrowCongr_symmMap₂ (e₁ : M ≃ₗ[R] M') (e₂ : N ≃ₗ[R] N')
    (f g : M →ₗ[R] N) :
    ((e₁.exteriorPower 2).arrowCongr (e₂.exteriorPower 2)) (exteriorPower.symmMap₂ f g) =
      exteriorPower.symmMap₂ (e₁.arrowCongr e₂ f) (e₁.arrowCongr e₂ g) := by
  rw [arrowCongr_eq_comp, arrowCongr_eq_comp, arrowCongr_eq_comp]
  simp only [LinearEquiv.exteriorPower_symm, LinearEquiv.exteriorPower_toLinearMap,
    exteriorPower.symmMap₂_comp_map, exteriorPower.map_comp_symmMap₂]

/-- Conjugating `exteriorPower.symmMap₂ f g` by `e.exteriorPower 2` conjugates each factor. -/
theorem exteriorPower_conj_symmMap₂ (e : M ≃ₗ[R] N) (f g : Module.End R M) :
    (e.exteriorPower 2).conj (exteriorPower.symmMap₂ f g) =
      exteriorPower.symmMap₂ (e.conj f) (e.conj g) :=
  exteriorPower_arrowCongr_symmMap₂ e e f g

end LinearEquiv

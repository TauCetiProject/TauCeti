/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.ToLin
public import TauCeti.LinearAlgebra.BilinearForm.Contact
import Mathlib.LinearAlgebra.Projection
import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis

/-!
# The linear normal form of a contact covector

On `Kⁿ × Kⁿ × K`, with coordinates `(q, p, z)`, the **standard contact covector** is `dz`
(`TauCeti.stdContactCovector`) and the **standard contact bilinear form** is `Σᵢ dqᵢ ∧ dpᵢ`,
`((q, p, z), (q', p', z')) ↦ q ⬝ᵥ p' - p ⬝ᵥ q'` (`TauCeti.stdContactBilinForm`). These are the
values at the origin of the standard contact form `dz - Σᵢ pᵢ dqᵢ` and of its exterior derivative.
The standard covector is contact for the standard form
(`TauCeti.isContact_stdContactCovector`), with Reeb vector `∂_z = (0, 0, 1)`
(`TauCeti.reebVector_stdContactCovector`).

This file proves that every contact covector is standard in suitable linear coordinates. If `a` is
contact for an alternating form `B` on a finite-dimensional space `V`, there is a linear
equivalence `e : V ≃ Kⁿ × Kⁿ × K` with `a = dz ∘ e` and `B = (Σᵢ dqᵢ ∧ dpᵢ) ∘ (e × e)`
(`Module.Dual.IsContact.exists_linearEquiv_eq_stdContact`). Conversely such coordinates make
`a` contact for `B` (`Module.Dual.isContact_iff_exists_linearEquiv_eq_stdContact`). Consequently
any two contact covectors for alternating forms on spaces of the same dimension are carried to each
other by a linear equivalence that also carries one form to the other
(`Module.Dual.IsContact.exists_linearEquiv_of_finrank_eq`).

The coordinates are built from the splitting `V = ker a ⊕ K r` along the Reeb vector `r`, and a
symplectic basis of the nondegenerate alternating form that `B` restricts to on `ker a`
(`LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J`). They map the Reeb vector to `∂_z`, as
both contactness and the Reeb vector are transported by linear equivalences
(`Module.Dual.isContact_comp_linearEquiv_compl₁₂_iff`,
`Module.Dual.IsContact.reebVector_comp_linearEquiv_compl₁₂`).

This is the pointwise normal form underlying the contact Darboux theorem: at a point of a contact
manifold, the contact form and its exterior derivative take the standard values in a suitable
basis of the tangent space.

## References

* H. Geiges, *An Introduction to Contact Topology*, Cambridge University Press, 2008,
  Section 2.5 (the linear algebra behind the contact Darboux theorem).
-/

public section

open Module

namespace TauCeti

section Model

variable (K : Type*) [CommRing K] (n : ℕ)

/-- The **standard contact covector** `dz` on `Kⁿ × Kⁿ × K`, with coordinates `(q, p, z)`. It is
the value at the origin of the standard contact form `dz - Σᵢ pᵢ dqᵢ`. -/
def stdContactCovector : Module.Dual K ((Fin n → K) × (Fin n → K) × K) :=
  LinearMap.snd K (Fin n → K) K ∘ₗ LinearMap.snd K (Fin n → K) ((Fin n → K) × K)

@[simp]
theorem stdContactCovector_apply (x : (Fin n → K) × (Fin n → K) × K) :
    stdContactCovector K n x = x.2.2 :=
  (rfl)

/-- The **standard contact bilinear form** `Σᵢ dqᵢ ∧ dpᵢ` on `Kⁿ × Kⁿ × K`, with coordinates
`(q, p, z)`: `((q, p, z), (q', p', z')) ↦ q ⬝ᵥ p' - p ⬝ᵥ q'`. It is the exterior derivative of the
standard contact form `dz - Σᵢ pᵢ dqᵢ`. -/
def stdContactBilinForm : LinearMap.BilinForm K ((Fin n → K) × (Fin n → K) × K) :=
  (dotProductBilin K K).compl₁₂ (LinearMap.fst K _ _)
      (LinearMap.fst K _ _ ∘ₗ LinearMap.snd K (Fin n → K) ((Fin n → K) × K)) -
    (dotProductBilin K K).compl₁₂
      (LinearMap.fst K _ _ ∘ₗ LinearMap.snd K (Fin n → K) ((Fin n → K) × K)) (LinearMap.fst K _ _)

@[simp]
theorem stdContactBilinForm_apply (x y : (Fin n → K) × (Fin n → K) × K) :
    stdContactBilinForm K n x y = x.1 ⬝ᵥ y.2.1 - x.2.1 ⬝ᵥ y.1 :=
  (rfl)

/-- The standard contact bilinear form is alternating. -/
theorem isAlt_stdContactBilinForm : (stdContactBilinForm K n).IsAlt := fun x ↦ by
  rw [stdContactBilinForm_apply, dotProduct_comm, sub_self]

end Model

variable {K : Type*} [Field K] {n : ℕ}

/-- The standard contact covector `dz` is contact for the standard bilinear form
`Σᵢ dqᵢ ∧ dpᵢ`. -/
theorem isContact_stdContactCovector (K : Type*) [Field K] (n : ℕ) :
    (stdContactCovector K n).IsContact (stdContactBilinForm K n) := by
  refine (Module.Dual.isContact_iff_of_isRefl (isAlt_stdContactBilinForm K n).isRefl).2
    ⟨fun h ↦ by simpa using LinearMap.congr_fun h (0, 0, 1), fun v hv hvw ↦ ?_⟩
  -- Test `v` against the kernel vectors `(0, eᵢ, 0)` and `(eᵢ, 0, 0)`.
  have hq (i : Fin n) : v.1 i = 0 := by
    simpa using hvw (0, Pi.single i 1, 0) rfl
  have hp (i : Fin n) : v.2.1 i = 0 := by
    simpa using hvw (Pi.single i 1, 0, 0) rfl
  exact Prod.ext (funext hq) (Prod.ext (funext hp) hv)

/-- The Reeb vector of the standard contact covector is `∂_z = (0, 0, 1)`. -/
@[simp]
theorem reebVector_stdContactCovector :
    (stdContactCovector K n).reebVector (stdContactBilinForm K n) = (0, 0, 1) :=
  ((isContact_stdContactCovector K n).eq_reebVector_iff_of_isAlt
    (isAlt_stdContactBilinForm K n)).2
    ⟨by simp, LinearMap.ext fun w ↦ by simp⟩ |>.symm

end TauCeti

namespace Module.Dual

open TauCeti

variable {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  {a : Module.Dual K V} {B : LinearMap.BilinForm K V}

/-! ### The normal form -/

/-- In the coordinates `Sum.elim p q` of a symplectic basis, the form with matrix `Matrix.J` is
`q ⬝ᵥ p' - p ⬝ᵥ q'`. -/
private theorem sumElim_dotProduct_J_mulVec_sumElim {n : ℕ} (p q p' q' : Fin n → K) :
    Sum.elim p q ⬝ᵥ (Matrix.J (Fin n) K).mulVec (Sum.elim p' q') = q ⬝ᵥ p' - p ⬝ᵥ q' := by
  rw [Matrix.J, Matrix.fromBlocks_mulVec, sumElim_dotProduct_sumElim]
  simp [Matrix.neg_mulVec]
  ring

variable [FiniteDimensional K V]

/-- **Linear normal form of a contact covector.** If `a` is contact for an alternating form `B` on
a finite-dimensional space `V`, there are linear coordinates `e : V ≃ Kⁿ × Kⁿ × K` in which `a` is
the standard contact covector `dz` and `B` is the standard form `Σᵢ dqᵢ ∧ dpᵢ`. Such coordinates
send the Reeb vector of `a` to `∂_z` (`Module.Dual.IsContact.reebVector_comp_linearEquiv_compl₁₂`,
`TauCeti.reebVector_stdContactCovector`). -/
theorem IsContact.exists_linearEquiv_eq_stdContact (hB : B.IsAlt) (h : a.IsContact B) :
    ∃ (n : ℕ) (e : V ≃ₗ[K] (Fin n → K) × (Fin n → K) × K),
      stdContactCovector K n ∘ₗ (e : V →ₗ[K] _) = a ∧
        (stdContactBilinForm K n).compl₁₂ (e : V →ₗ[K] _) e = B := by
  have hr : a.reebVector B ≠ 0 := h.reebVector_ne_zero
  have hrB (v : V) : B (a.reebVector B) v = 0 := h.apply_reebVector_left hB v
  have hBr (v : V) : B v (a.reebVector B) = 0 := h.apply_reebVector_right hB v
  -- A symplectic basis `c` of the hyperplane `ker a`, indexed so that `c (inl i) = pᵢ` and
  -- `c (inr i) = qᵢ`.
  obtain ⟨n, c, hc⟩ := LinearMap.BilinForm.IsAlt.exists_basis_toMatrix_eq_J
    (B := B.restrict (LinearMap.ker a)) (fun v ↦ hB v) h.nondegenerate_restrict
  -- The inverse coordinates `(q, p, z) ↦ Σᵢ qᵢ • c (inr i) + Σᵢ pᵢ • c (inl i) + z • r`, assembled
  -- from the splitting `V = ker a ⊕ K r`.
  set f : ((Fin n → K) × (Fin n → K) × K) ≃ₗ[K] V :=
    (LinearEquiv.prodAssoc K (Fin n → K) (Fin n → K) K).symm ≪≫ₗ
      ((LinearEquiv.prodComm K (Fin n → K) (Fin n → K) ≪≫ₗ
          (LinearEquiv.sumArrowLequivProdArrow (Fin n) (Fin n) K K).symm ≪≫ₗ
          c.equivFun.symm).prodCongr
        (LinearEquiv.toSpanNonzeroSingleton K V _ hr)) ≪≫ₗ
      Submodule.prodEquivOfIsCompl _ _ h.isCompl_ker_span_reebVector
  set w : (Fin n → K) × (Fin n → K) × K → LinearMap.ker a := fun x ↦
    c.equivFun.symm (Sum.elim x.2.1 x.1)
  have hf (x : (Fin n → K) × (Fin n → K) × K) : f x = (w x : V) + x.2.2 • a.reebVector B := by
    obtain ⟨q, p, z⟩ := x
    simp only [f, w, LinearEquiv.trans_apply, LinearEquiv.prodCongr_apply,
      Submodule.coe_prodEquivOfIsCompl', LinearEquiv.toSpanNonzeroSingleton_apply]
    -- The reassociation, swap and `Sum.elim` steps are the identity on these coordinates.
    rfl
  have ha (x : (Fin n → K) × (Fin n → K) × K) : a (f x) = x.2.2 := by
    rw [hf, map_add, LinearMap.mem_ker.1 (w x).2, map_smul, h.apply_reebVector, smul_eq_mul,
      mul_one, zero_add]
  have hw (x : (Fin n → K) × (Fin n → K) × K) : ⇑(c.repr (w x)) = Sum.elim x.2.1 x.1 := by
    ext s
    rw [← c.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hB' (x y : (Fin n → K) × (Fin n → K) × K) :
      B (f x) (f y) = x.1 ⬝ᵥ y.2.1 - x.2.1 ⬝ᵥ y.1 := by
    -- The Reeb vector lies in the kernel of `B`; on `ker a`, `B` has the matrix `J` in `c`.
    have hwB : B (w x) (w y) =
        Sum.elim x.2.1 x.1 ⬝ᵥ (Matrix.J (Fin n) K).mulVec (Sum.elim y.2.1 y.1) := by
      rw [← hw, ← hw, ← Matrix.toBilin'_apply', Matrix.toBilin'_apply, ← Matrix.toBilin_apply,
        ← hc, Matrix.toBilin_toMatrix, LinearMap.BilinForm.restrict_apply,
        LinearMap.domRestrict_apply]
    simp only [hf, map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hrB, hBr,
      smul_zero, add_zero, hwB, sumElim_dotProduct_J_mulVec_sumElim]
  refine ⟨n, f.symm, LinearMap.ext fun v ↦ ?_, LinearMap.ext₂ fun v v' ↦ ?_⟩
  · simpa using (ha (f.symm v)).symm
  · simpa using (hB' (f.symm v) (f.symm v')).symm

/-- **Contact covectors are those with standard linear coordinates.** For an alternating form `B`
on a finite-dimensional space, `a` is contact for `B` exactly when some linear coordinates
`e : V ≃ Kⁿ × Kⁿ × K` make `a` the standard covector `dz` and `B` the standard form
`Σᵢ dqᵢ ∧ dpᵢ`. -/
theorem isContact_iff_exists_linearEquiv_eq_stdContact (hB : B.IsAlt) :
    a.IsContact B ↔ ∃ (n : ℕ) (e : V ≃ₗ[K] (Fin n → K) × (Fin n → K) × K),
      stdContactCovector K n ∘ₗ (e : V →ₗ[K] _) = a ∧
        (stdContactBilinForm K n).compl₁₂ (e : V →ₗ[K] _) e = B := by
  refine ⟨IsContact.exists_linearEquiv_eq_stdContact hB, ?_⟩
  rintro ⟨n, e, rfl, rfl⟩
  exact (isContact_comp_linearEquiv_compl₁₂_iff e).2 (isContact_stdContactCovector K n)

/-- **Uniqueness of linear contact structures.** Two contact covectors for alternating forms, on
finite-dimensional spaces of the same dimension, are carried to each other by a linear
equivalence which also carries one form to the other. -/
theorem IsContact.exists_linearEquiv_of_finrank_eq [FiniteDimensional K V'] (hB : B.IsAlt)
    (h : a.IsContact B) {a' : Module.Dual K V'} {B' : LinearMap.BilinForm K V'} (hB' : B'.IsAlt)
    (h' : a'.IsContact B') (hV : finrank K V = finrank K V') :
    ∃ e : V ≃ₗ[K] V', a' ∘ₗ (e : V →ₗ[K] V') = a ∧ B'.compl₁₂ (e : V →ₗ[K] V') e = B := by
  obtain ⟨n, e, rfl, rfl⟩ := h.exists_linearEquiv_eq_stdContact hB
  obtain ⟨n', e', rfl, rfl⟩ := h'.exists_linearEquiv_eq_stdContact hB'
  -- The model `Kⁿ × Kⁿ × K` has dimension `2 n + 1`, so `n = n'`.
  obtain rfl : n = n' := by
    have := e.finrank_eq
    have := e'.finrank_eq
    simp only [finrank_prod, finrank_fin_fun, finrank_self] at *
    omega
  refine ⟨e.trans e'.symm, LinearMap.ext fun v ↦ ?_, LinearMap.ext₂ fun v w ↦ ?_⟩ <;> simp

end Module.Dual

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.Orientation
public import TauCeti.LinearAlgebra.Determinant.Exact
import TauCeti.LinearAlgebra.Complex.Finrank
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.ExteriorPower.Basis

/-!
# Complex orientations of real determinant lines

A finite-dimensional complex vector space `E` has a canonical real orientation, the orientation of
the real basis `(b₀, I • b₀, b₁, I • b₁, …)` underlying any complex basis `b`
(`TauCeti.complexOrientation`). This file expresses it on the real determinant line
`det E = ⋀^top_ℝ E` (`TauCeti.detLine`): an element of `det E` is **complex positive**
(`TauCeti.IsComplexPositive`) if it is a positive multiple of `b₀ ∧ I • b₀ ∧ b₁ ∧ I • b₁ ∧ ⋯` for a
complex basis `b`. Two complex bases give exterior products differing by the squared modulus of
their complex determinant (`TauCeti.ιMulti_complexToRealFamily_eq_normSq_det_smul`), so every
complex basis may be used (`TauCeti.isComplexPositive_iff`), and exactly one of `x` and `-x` is
complex positive for each nonzero `x`. A functional on `det E` is complex positive
(`TauCeti.IsComplexPositiveDual`) if it is positive on the complex positive elements, and an
element of `det E ⊗ (det F)^*` is complex positive (`TauCeti.IsComplexPositiveTMulDual`) if it is
`x ⊗ φ` with `x` and `φ` complex positive. For finite-dimensional `E` and `F`, each of these sets
is an open half-line.

The determinant line of a linear map `T` with finite-dimensional kernel and cokernel is
`det (ker T) ⊗ (det (coker T))^*` (`LinearMap.detLine`), and for a complex-linear `T` both factors
are complex vector spaces. The point of this file is that the canonical identifications of real
determinant lines along exact sequences respect complex orientations, when the sequences consist of
complex vector spaces and complex-linear maps:

* for a short exact sequence `0 → U → V → W → 0`, the isomorphism `det U ⊗ det W ≃ det V`
  (`TauCeti.detLineShortExactEquiv`) maps complex positive elements to complex positive elements
  (`TauCeti.isComplexPositive_detLineShortExactEquiv_tmul`);
* for an exact sequence `0 → A → B → C → D → 0`, the isomorphism
  `det B ⊗ (det C)^* ≃ det A ⊗ (det D)^*` (`TauCeti.detLineFourTermEquiv`) maps complex positive
  elements to complex positive elements
  (`TauCeti.isComplexPositiveTMulDual_detLineFourTermEquiv`).

No sign corrections enter, because complex vector spaces have even real dimension. The second
statement is the form needed for Fredholm operators. A stabilization `D₂ : Λ → F` of a
complex-linear operator `D₁ : E → F` by a finite-dimensional complex space `Λ` produces the exact
sequence `0 → ker D₁ → ker (D₁.coprod D₂) → Λ → coker D₁ → 0` of complex vector spaces and
complex-linear maps, and `ContinuousLinearMap.detLineCoprodEquiv` is
`TauCeti.detLineFourTermEquiv` for its real restriction. Complex positivity of the determinant line
of `D₁` thus corresponds to complex positivity of `det (ker (D₁.coprod D₂)) ⊗ (det Λ)^*`. This is
the input for orienting the determinant line bundle of a family of complex-linear Fredholm
operators, such as a complex Dirac operator or the complex-linear part of the anti-self-dual
deformation operator of an almost Hermitian four-manifold, by the complex orientations of its
fibres.

## Main definitions

* `TauCeti.IsComplexPositive`, `TauCeti.IsComplexPositiveDual`,
  `TauCeti.IsComplexPositiveTMulDual`: the complex orientations of `det E`, of `(det E)^*` and of
  `det E ⊗ (det F)^*`.

## Main results

* `TauCeti.isComplexPositive_iff`: complex positivity is computed by any complex basis.
* `TauCeti.isComplexPositive_iff_of_orientation_eq`: complex positivity is
  `TauCeti.complexOrientation`, computed by any real basis in that orientation.
* `TauCeti.IsComplexPositive.exists_pos_smul_eq`, `TauCeti.IsComplexPositive.not_neg`,
  `TauCeti.isComplexPositive_or_isComplexPositive_neg`: complex positivity is an orientation of
  the line `det E`; similarly for `(det E)^*` and `det E ⊗ (det F)^*`.
* `TauCeti.isComplexPositive_detLineShortExactEquiv_tmul`: compatibility with short exact
  sequences.
* `TauCeti.isComplexPositiveTMulDual_detLineFourTermEquiv`: compatibility with four-term exact
  sequences, hence with stabilizations of complex-linear Fredholm operators.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines, and the canonical
  orientation of the determinant line of a complex-linear Fredholm operator).
-/

public section

noncomputable section

open Module TensorProduct

namespace TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℂ E] [Module ℝ E] [IsScalarTower ℝ ℂ E]
  [AddCommGroup F] [Module ℂ F] [Module ℝ F] [IsScalarTower ℝ ℂ F]

/-! ### Exterior products of real families underlying complex families -/

section Family

variable {m n : ℕ}

/-- The exterior products of the real families underlying two complex bases differ by the squared
modulus of the complex determinant between the bases. In particular they are positive multiples
of each other. -/
theorem ιMulti_complexToRealFamily_eq_normSq_det_smul (b c : Basis (Fin n) ℂ E) :
    ExteriorAlgebra.ιMulti ℝ (2 * n) (complexToRealFamily ⇑c) =
      Complex.normSq (b.det c) • ExteriorAlgebra.ιMulti ℝ (2 * n) (complexToRealFamily ⇑b) := by
  set e := complexRealIndexEquiv n
  have hdet : (b.complexToReal.reindex e).det (complexToRealFamily ⇑c) =
      Complex.normSq (b.det c) := by
    rw [← c.coe_complexToReal_reindex_complexRealIndexEquiv, Basis.det_reindex,
      Basis.coe_reindex, Function.comp_assoc, Equiv.symm_comp_self, Function.comp_id,
      Basis.det_complexToReal]
  have h := congrArg Subtype.val
    ((b.complexToReal.reindex e).exteriorPower_ιMulti_eq_det_smul (complexToRealFamily ⇑c))
  rwa [hdet, b.coe_complexToReal_reindex_complexRealIndexEquiv] at h

/-- The exterior product of the image under a complex-linear map `f` of the real family underlying
`u`, followed by the real family underlying `v`, is the exterior product of the real family
underlying the appended complex family `(f ∘ u, v)`. The real index types may be any of the right
sizes. -/
theorem ιMulti_append_comp_complexToRealFamily {a b : ℕ} (f : E →ₗ[ℂ] F) (u : Fin m → E)
    (v : Fin n → F) (ha : a = 2 * m) (hb : b = 2 * n) :
    ExteriorAlgebra.ιMulti ℝ (a + b)
        (Fin.append ((f.restrictScalars ℝ) ∘ complexToRealFamily u ∘ Fin.cast ha)
          (complexToRealFamily v ∘ Fin.cast hb)) =
      ExteriorAlgebra.ιMulti ℝ (2 * (m + n)) (complexToRealFamily (Fin.append (f ∘ u) v)) := by
  rw [LinearMap.coe_restrictScalars, ← Function.comp_assoc, ← complexToRealFamily_comp,
    Fin.append_cast_left, Fin.append_cast_right, append_complexToRealFamily]
  simp

end Family

/-! ### The complex orientation of a determinant line -/

section Positive

variable {n : ℕ} {x y : detLine ℝ E}

/-- An element of the real determinant line `det E = ⋀^top_ℝ E` of a complex vector space is
**complex positive** if it is a positive multiple of `b₀ ∧ I • b₀ ∧ b₁ ∧ I • b₁ ∧ ⋯` for a
complex basis `b` of `E`. Then the same holds for every complex basis
(`TauCeti.isComplexPositive_iff`). The real bases `(b₀, I • b₀, b₁, I • b₁, …)` are those defining
the canonical orientation `TauCeti.complexOrientation`, so this is that orientation read on the
determinant line. -/
def IsComplexPositive (x : detLine ℝ E) : Prop :=
  ∃ (n : ℕ) (b : Basis (Fin n) ℂ E) (c : ℝ), 0 < c ∧
    (x : ExteriorAlgebra ℝ E) = c • ExteriorAlgebra.ιMulti ℝ (2 * n) (complexToRealFamily ⇑b)

/-- **Complex positivity is computed by any complex basis**: an element of `det E` is complex
positive exactly when it is a positive multiple of `b₀ ∧ I • b₀ ∧ b₁ ∧ I • b₁ ∧ ⋯` for the given
complex basis `b`. -/
theorem isComplexPositive_iff (b : Basis (Fin n) ℂ E) :
    IsComplexPositive x ↔ ∃ c : ℝ, 0 < c ∧
      (x : ExteriorAlgebra ℝ E) =
        c • ExteriorAlgebra.ιMulti ℝ (2 * n) (complexToRealFamily ⇑b) := by
  refine ⟨?_, fun ⟨c, hc, hx⟩ ↦ ⟨n, b, c, hc, hx⟩⟩
  rintro ⟨m, b', c, hc, hx⟩
  obtain rfl : m = n := by
    simpa using (finrank_eq_card_basis b').symm.trans (finrank_eq_card_basis b)
  refine ⟨c * Complex.normSq (b.det b'),
    mul_pos hc (Complex.normSq_pos.2 (b.isUnit_det b').ne_zero), ?_⟩
  rw [hx, ιMulti_complexToRealFamily_eq_normSq_det_smul b b', smul_smul]

/-- **Complex positivity is the canonical orientation** `TauCeti.complexOrientation` read on the
determinant line: for a real basis `e` of `E` in the canonical orientation, an element of `det E` is
complex positive exactly when it is a positive multiple of `e₀ ∧ e₁ ∧ ⋯`. -/
theorem isComplexPositive_iff_of_orientation_eq [FiniteDimensional ℂ E]
    {e : Basis (Fin (2 * finrank ℂ E)) ℝ E} (he : e.orientation = complexOrientation E) :
    IsComplexPositive x ↔ ∃ c : ℝ, 0 < c ∧
      (x : ExteriorAlgebra ℝ E) = c • ExteriorAlgebra.ιMulti ℝ _ ⇑e := by
  set b := finBasis ℂ E
  set e₀ := b.complexToReal.reindex (complexRealIndexEquiv (finrank ℂ E))
  -- `e` and the real basis `e₀` underlying `b` define the same orientation.
  have hdet : 0 < e₀.det e := by
    rw [← Basis.orientation_eq_iff_det_pos, he, b.complexOrientation_eq, Basis.orientation_reindex]
  have he₀ : ExteriorAlgebra.ιMulti ℝ _ ⇑e =
      e₀.det e • ExteriorAlgebra.ιMulti ℝ _ (complexToRealFamily ⇑b) := by
    have h := congrArg Subtype.val (e₀.exteriorPower_ιMulti_eq_det_smul e)
    rwa [b.coe_complexToReal_reindex_complexRealIndexEquiv] at h
  rw [isComplexPositive_iff b, he₀]
  refine ⟨fun ⟨c, hc, hx⟩ ↦ ⟨c / e₀.det e, div_pos hc hdet, ?_⟩,
    fun ⟨c, hc, hx⟩ ↦ ⟨c * e₀.det e, mul_pos hc hdet, by rw [hx, smul_smul]⟩⟩
  rw [hx, smul_smul, div_mul_cancel₀ _ hdet.ne']

omit [IsScalarTower ℝ ℂ E] in
/-- An element whose image in the exterior algebra is a positive multiple of the exterior product of
the real family underlying a complex basis, given as a linearly independent family of the right
length, is complex positive. -/
theorem isComplexPositive_of_coe_eq_smul [FiniteDimensional ℂ E] {v : Fin n → E}
    (hv : LinearIndependent ℂ v) (hn : n = finrank ℂ E) {c : ℝ} (hc : 0 < c)
    (hx : (x : ExteriorAlgebra ℝ E) =
      c • ExteriorAlgebra.ιMulti ℝ (2 * n) (complexToRealFamily v)) :
    IsComplexPositive x :=
  ⟨n, basisOfLinearIndependentOfCardEqFinrank' v hv (by simp [hn]), c, hc, by
    rwa [coe_basisOfLinearIndependentOfCardEqFinrank']⟩

omit [IsScalarTower ℝ ℂ E] in
/-- Complex positive elements form a cone: a positive multiple of a complex positive element is
complex positive. -/
theorem IsComplexPositive.smul (hx : IsComplexPositive x) {c : ℝ} (hc : 0 < c) :
    IsComplexPositive (c • x) := by
  obtain ⟨n, b, d, hd, hx⟩ := hx
  exact ⟨n, b, c * d, mul_pos hc hd, by rw [Submodule.coe_smul, hx, smul_smul]⟩

/-- A complex positive element of `det E` is nonzero. -/
theorem IsComplexPositive.ne_zero (hx : IsComplexPositive x) : x ≠ 0 := by
  obtain ⟨n, b, c, hc, hx⟩ := hx
  have hb :
      (exteriorPower.ιMulti ℝ (2 * n) (complexToRealFamily ⇑b) : ExteriorAlgebra ℝ E) ≠ 0 := by
    rw [Ne, ZeroMemClass.coe_eq_zero, ← Ne, exteriorPower.ιMulti_ne_zero_iff,
      ← b.coe_complexToReal_reindex_complexRealIndexEquiv]
    exact Basis.linearIndependent _
  rintro rfl
  rw [ZeroMemClass.coe_zero, eq_comm, smul_eq_zero] at hx
  exact hb (hx.resolve_left hc.ne')

/-- Every finite-dimensional complex vector space has a complex positive element of its real
determinant line. -/
theorem exists_isComplexPositive [FiniteDimensional ℂ E] : ∃ x : detLine ℝ E, IsComplexPositive x :=
  ⟨exteriorPower.ιMulti ℝ _ (complexToRealFamily ⇑(finBasis ℂ E) ∘
      Fin.cast finrank_real_eq_two_mul_finrank_complex),
    finrank ℂ E, finBasis ℂ E, 1, one_pos, by simp⟩

/-- Two complex positive elements of `det E` differ by a positive factor. -/
theorem IsComplexPositive.exists_pos_smul_eq (hx : IsComplexPositive x) (hy : IsComplexPositive y) :
    ∃ c : ℝ, 0 < c ∧ y = c • x := by
  obtain ⟨n, b, c, hc, hx⟩ := hx
  obtain ⟨d, hd, hy⟩ := (isComplexPositive_iff b).1 hy
  refine ⟨d / c, div_pos hd hc, Subtype.ext ?_⟩
  rw [Submodule.coe_smul, hx, hy, smul_smul, div_mul_cancel₀ _ hc.ne']

/-- The negative of a complex positive element is not complex positive: complex positivity is an
orientation of `det E`, not a vacuous condition. -/
theorem IsComplexPositive.not_neg (hx : IsComplexPositive x) : ¬ IsComplexPositive (-x) := by
  intro hnx
  obtain ⟨c, hc, h⟩ := hx.exists_pos_smul_eq hnx
  have : (1 + c) • x = 0 := by rw [add_smul, one_smul, ← h, add_neg_cancel]
  exact hx.ne_zero ((smul_eq_zero.1 this).resolve_left (by positivity))

/-- Exactly one of `x` and `-x` is complex positive for each nonzero element `x` of the line
`det E`; that at most one is follows from `TauCeti.IsComplexPositive.not_neg`. -/
theorem isComplexPositive_or_isComplexPositive_neg [FiniteDimensional ℂ E] (hx : x ≠ 0) :
    IsComplexPositive x ∨ IsComplexPositive (-x) := by
  have : Module.Finite ℝ E := Module.Finite.trans ℂ E
  obtain ⟨x₀, hx₀⟩ := exists_isComplexPositive (E := E)
  obtain ⟨t, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' x₀ hx₀.ne_zero).1 (finrank_detLine ℝ E) x
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · exact Or.inr (by rw [← neg_smul]; exact hx₀.smul (neg_pos.2 ht))
  · exact absurd (zero_smul ℝ x₀) hx
  · exact Or.inl (hx₀.smul ht)

end Positive

/-! ### Complex positive functionals and tensors -/

section Dual

variable {x : detLine ℝ E} {φ ψ : Dual ℝ (detLine ℝ E)}

/-- A functional on the real determinant line of a complex vector space is **complex positive** if
it is positive on every complex positive element. For finite-dimensional `E`, these functionals form
the half-line of the dual orientation of `(det E)^*`. -/
def IsComplexPositiveDual (φ : Dual ℝ (detLine ℝ E)) : Prop :=
  ∀ x : detLine ℝ E, IsComplexPositive x → 0 < φ x

/-- A functional is complex positive as soon as it is positive at one complex positive element. -/
theorem IsComplexPositive.isComplexPositiveDual_iff (hx : IsComplexPositive x) :
    IsComplexPositiveDual φ ↔ 0 < φ x := by
  refine ⟨fun hφ ↦ hφ x hx, fun h y hy ↦ ?_⟩
  obtain ⟨c, hc, rfl⟩ := hx.exists_pos_smul_eq hy
  rw [map_smul, smul_eq_mul]
  exact mul_pos hc h

/-- A functional taking the value `1` at a complex positive element is complex positive. -/
theorem IsComplexPositive.isComplexPositiveDual_of_apply_eq_one (hx : IsComplexPositive x)
    (hφ : φ x = 1) : IsComplexPositiveDual φ :=
  hx.isComplexPositiveDual_iff.2 (hφ ▸ one_pos)

/-- Every finite-dimensional complex vector space has a complex positive functional on its real
determinant line. -/
theorem exists_isComplexPositiveDual [FiniteDimensional ℂ E] :
    ∃ φ : Dual ℝ (detLine ℝ E), IsComplexPositiveDual φ := by
  obtain ⟨x, hx⟩ := exists_isComplexPositive (E := E)
  obtain ⟨φ, hφ⟩ := Projective.exists_dual_eq_one ℝ hx.ne_zero
  exact ⟨φ, hx.isComplexPositiveDual_of_apply_eq_one hφ⟩

omit [IsScalarTower ℝ ℂ E] in
/-- A positive multiple of a complex positive functional is complex positive. -/
theorem IsComplexPositiveDual.smul (hφ : IsComplexPositiveDual φ) {c : ℝ} (hc : 0 < c) :
    IsComplexPositiveDual (c • φ) := fun x hx ↦ by
  rw [LinearMap.smul_apply, smul_eq_mul]
  exact mul_pos hc (hφ x hx)

/-- A complex positive functional on the determinant line of a finite-dimensional complex vector
space is nonzero. -/
theorem IsComplexPositiveDual.ne_zero [FiniteDimensional ℂ E] (hφ : IsComplexPositiveDual φ) :
    φ ≠ 0 := by
  obtain ⟨x, hx⟩ := exists_isComplexPositive (E := E)
  rintro rfl
  exact (hφ x hx).ne' rfl

/-- The negative of a complex positive functional is not complex positive. -/
theorem IsComplexPositiveDual.not_neg [FiniteDimensional ℂ E] (hφ : IsComplexPositiveDual φ) :
    ¬ IsComplexPositiveDual (-φ) := fun hnφ ↦ by
  obtain ⟨x, hx⟩ := exists_isComplexPositive (E := E)
  have h := hnφ x hx
  rw [LinearMap.neg_apply, neg_pos] at h
  exact (hφ x hx).not_gt h

/-- Exactly one of `φ` and `-φ` is complex positive for each nonzero functional `φ` on `det E`;
that at most one is follows from `TauCeti.IsComplexPositiveDual.not_neg`. -/
theorem isComplexPositiveDual_or_isComplexPositiveDual_neg [FiniteDimensional ℂ E] (hφ : φ ≠ 0) :
    IsComplexPositiveDual φ ∨ IsComplexPositiveDual (-φ) := by
  have : Module.Finite ℝ E := Module.Finite.trans ℂ E
  obtain ⟨x, hx⟩ := exists_isComplexPositive (E := E)
  -- A functional on the line `det E` vanishing at the nonzero `x` vanishes.
  have hφx : φ x ≠ 0 := fun h ↦ hφ <| LinearMap.ext fun y ↦ by
    obtain ⟨t, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' x hx.ne_zero).1 (finrank_detLine ℝ E) y
    simp [h]
  rcases hφx.lt_or_gt with h | h
  · exact Or.inr (hx.isComplexPositiveDual_iff.2 (by simpa using h))
  · exact Or.inl (hx.isComplexPositiveDual_iff.2 h)

/-- Two complex positive functionals on `det E` differ by a positive factor. -/
theorem IsComplexPositiveDual.exists_pos_smul_eq [FiniteDimensional ℂ E]
    (hφ : IsComplexPositiveDual φ) (hψ : IsComplexPositiveDual ψ) :
    ∃ c : ℝ, 0 < c ∧ ψ = c • φ := by
  have : Module.Finite ℝ E := Module.Finite.trans ℂ E
  obtain ⟨x, hx⟩ := exists_isComplexPositive (E := E)
  have hφx := hφ x hx
  refine ⟨ψ x / φ x, div_pos (hψ x hx) hφx, LinearMap.ext fun y ↦ ?_⟩
  obtain ⟨t, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' x hx.ne_zero).1 (finrank_detLine ℝ E) y
  simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
  field_simp

end Dual

section TMulDual

variable {t s : detLine ℝ E ⊗[ℝ] Dual ℝ (detLine ℝ F)}

/-- An element of `det E ⊗ (det F)^*`, the shape of the determinant line
`det (ker T) ⊗ (det (coker T))^*` of a linear map, is **complex positive** if it is `x ⊗ φ` for a
complex positive `x ∈ det E` and a complex positive functional `φ` on `det F`. -/
def IsComplexPositiveTMulDual (t : detLine ℝ E ⊗[ℝ] Dual ℝ (detLine ℝ F)) : Prop :=
  ∃ (x : detLine ℝ E) (φ : Dual ℝ (detLine ℝ F)), IsComplexPositive x ∧
    IsComplexPositiveDual φ ∧ t = x ⊗ₜ φ

omit [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] in
/-- The tensor product of a complex positive element and a complex positive functional is complex
positive. -/
theorem IsComplexPositive.isComplexPositiveTMulDual_tmul {x : detLine ℝ E}
    {φ : Dual ℝ (detLine ℝ F)} (hx : IsComplexPositive x) (hφ : IsComplexPositiveDual φ) :
    IsComplexPositiveTMulDual (x ⊗ₜ φ) :=
  ⟨x, φ, hx, hφ, rfl⟩

/-- Every pair of finite-dimensional complex vector spaces has a complex positive element of
`det E ⊗ (det F)^*`. -/
theorem exists_isComplexPositiveTMulDual [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] :
    ∃ t : detLine ℝ E ⊗[ℝ] Dual ℝ (detLine ℝ F), IsComplexPositiveTMulDual t := by
  obtain ⟨x, hx⟩ := exists_isComplexPositive (E := E)
  obtain ⟨φ, hφ⟩ := exists_isComplexPositiveDual (E := F)
  exact ⟨_, hx.isComplexPositiveTMulDual_tmul hφ⟩

omit [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] in
/-- A positive multiple of a complex positive element of `det E ⊗ (det F)^*` is complex
positive. -/
theorem IsComplexPositiveTMulDual.smul (ht : IsComplexPositiveTMulDual t) {c : ℝ} (hc : 0 < c) :
    IsComplexPositiveTMulDual (c • t) := by
  obtain ⟨x, φ, hx, hφ, rfl⟩ := ht
  exact ⟨c • x, φ, hx.smul hc, hφ, (smul_tmul' c x φ).symm⟩

/-- Two complex positive elements of `det E ⊗ (det F)^*` differ by a positive factor. -/
theorem IsComplexPositiveTMulDual.exists_pos_smul_eq [FiniteDimensional ℂ F]
    (ht : IsComplexPositiveTMulDual t) (hs : IsComplexPositiveTMulDual s) :
    ∃ c : ℝ, 0 < c ∧ s = c • t := by
  obtain ⟨x, φ, hx, hφ, rfl⟩ := ht
  obtain ⟨y, ψ, hy, hψ, rfl⟩ := hs
  obtain ⟨a, ha, rfl⟩ := hx.exists_pos_smul_eq hy
  obtain ⟨b, hb, rfl⟩ := hφ.exists_pos_smul_eq hψ
  exact ⟨a * b, mul_pos ha hb, smul_tmul_smul a b x φ⟩

/-- A complex positive element of `det E ⊗ (det F)^*` is nonzero, for finite-dimensional `F`. -/
theorem IsComplexPositiveTMulDual.ne_zero [FiniteDimensional ℂ F]
    (ht : IsComplexPositiveTMulDual t) : t ≠ 0 := by
  obtain ⟨x, φ, hx, hφ, rfl⟩ := ht
  obtain ⟨y, hy⟩ := exists_isComplexPositive (E := F)
  obtain ⟨ξ, hξ⟩ := Projective.exists_dual_eq_one ℝ hx.ne_zero
  -- Pairing the first factor with `ξ` and evaluating the second at `y` sends `x ⊗ φ` to `φ y`.
  intro h
  have h' := congrArg (TensorProduct.lift ((LinearMap.mul ℝ ℝ).compl₁₂ ξ (Dual.eval ℝ _ y))) h
  simp only [lift.tmul, LinearMap.compl₁₂_apply, Dual.eval_apply, LinearMap.mul_apply', hξ,
    one_mul, map_zero] at h'
  exact (hφ y hy).ne' h'

/-- The negative of a complex positive element of `det E ⊗ (det F)^*` is not complex positive. -/
theorem IsComplexPositiveTMulDual.not_neg [FiniteDimensional ℂ F]
    (ht : IsComplexPositiveTMulDual t) : ¬ IsComplexPositiveTMulDual (-t) := by
  intro hnt
  obtain ⟨c, hc, h⟩ := ht.exists_pos_smul_eq hnt
  have : (1 + c) • t = 0 := by
    rw [add_smul, one_smul, ← h]
    exact add_neg_cancel t
  exact ht.ne_zero ((smul_eq_zero.1 this).resolve_left (by positivity))

/-- Exactly one of `t` and `-t` is complex positive for each nonzero element `t` of the line
`det E ⊗ (det F)^*`; that at most one is follows from
`TauCeti.IsComplexPositiveTMulDual.not_neg`. -/
theorem isComplexPositiveTMulDual_or_isComplexPositiveTMulDual_neg [FiniteDimensional ℂ E]
    [FiniteDimensional ℂ F] (ht : t ≠ 0) :
    IsComplexPositiveTMulDual t ∨ IsComplexPositiveTMulDual (-t) := by
  have : Module.Finite ℝ E := Module.Finite.trans ℂ E
  have : Module.Finite ℝ F := Module.Finite.trans ℂ F
  obtain ⟨t₀, ht₀⟩ := exists_isComplexPositiveTMulDual (E := E) (F := F)
  have hrank : finrank ℝ (detLine ℝ E ⊗[ℝ] Dual ℝ (detLine ℝ F)) = 1 := by
    simp [finrank_tensorProduct]
  obtain ⟨s, rfl⟩ := (finrank_eq_one_iff_of_ne_zero' t₀ ht₀.ne_zero).1 hrank t
  rcases lt_trichotomy s 0 with hs | rfl | hs
  · exact Or.inr (by rw [← neg_smul]; exact ht₀.smul (neg_pos.2 hs))
  · exact absurd (zero_smul ℝ t₀) ht
  · exact Or.inl (ht₀.smul hs)

end TMulDual

/-! ### Exact sequences of complex vector spaces -/

section ShortExact

variable {U V W : Type*} [AddCommGroup U] [Module ℂ U] [Module ℝ U] [IsScalarTower ℝ ℂ U]
  [AddCommGroup V] [Module ℂ V] [Module ℝ V] [IsScalarTower ℝ ℂ V]
  [AddCommGroup W] [Module ℂ W] [Module ℝ W] [IsScalarTower ℝ ℂ W]
  -- Real finite-dimensionality follows from the complex one through the scalar tower, but
  -- `TauCeti.detLineShortExactEquiv` takes it as an instance argument.
  [FiniteDimensional ℝ U] [FiniteDimensional ℝ W]
  {f : U →ₗ[ℂ] V} {g : V →ₗ[ℂ] W}

/-- **Short exact sequences respect complex orientations.** For a short exact sequence
`0 → U → V → W → 0` of complex vector spaces and complex-linear maps, the identification
`det U ⊗ det W ≃ det V` of real determinant lines (`TauCeti.detLineShortExactEquiv`) sends `x ⊗ y`,
for complex positive `x` and `y`, to a complex positive element. -/
theorem isComplexPositive_detLineShortExactEquiv_tmul
    (hf : Function.Injective (f.restrictScalars ℝ))
    (hfg : Function.Exact (f.restrictScalars ℝ) (g.restrictScalars ℝ))
    (hg : Function.Surjective (g.restrictScalars ℝ)) {x : detLine ℝ U} {y : detLine ℝ W}
    (hx : IsComplexPositive x) (hy : IsComplexPositive y) :
    IsComplexPositive (detLineShortExactEquiv hf hfg hg (x ⊗ₜ y)) := by
  -- The hypotheses on the real restrictions are the same statements about `f` and `g`.
  have hfC : Function.Injective f := hf
  have hfgC : Function.Exact f g := hfg
  have hgC : Function.Surjective g := hg
  have : FiniteDimensional ℂ U := Module.Finite.of_restrictScalars_finite ℝ ℂ U
  have : FiniteDimensional ℂ W := Module.Finite.of_restrictScalars_finite ℝ ℂ W
  have : FiniteDimensional ℂ V := finiteDimensional_of_exact hfgC
  set bU := finBasis ℂ U
  set bW := finBasis ℂ W
  obtain ⟨c, hc, hxc⟩ := (isComplexPositive_iff bU).1 hx
  obtain ⟨d, hd, hyd⟩ := (isComplexPositive_iff bW).1 hy
  -- Lift the basis of `W` to `V`; with the image of the basis of `U` it is a basis of `V`.
  set v : Fin (finrank ℂ W) → V := Function.surjInv hgC ∘ bW
  have hv : g ∘ v = bW := funext fun i ↦ Function.surjInv_eq hgC _
  have hli : LinearIndependent ℂ (Fin.append (f ∘ bU) v) :=
    hfgC.linearIndependent_append hfC bU.linearIndependent (hv ▸ bW.linearIndependent)
  have hU := finrank_real_eq_two_mul_finrank_complex (V := U)
  have hW := finrank_real_eq_two_mul_finrank_complex (V := W)
  -- Write `x` and `y` as exterior products of real families of the right lengths.
  have hx' : x = c • exteriorPower.ιMulti ℝ _ (complexToRealFamily ⇑bU ∘ Fin.cast hU) :=
    Subtype.ext (by simp [hxc])
  have hy' : y = d • exteriorPower.ιMulti ℝ _
      ((g.restrictScalars ℝ) ∘ complexToRealFamily v ∘ Fin.cast hW) :=
    Subtype.ext (by simp [hyd, ← Function.comp_assoc, ← complexToRealFamily_comp, hv])
  refine isComplexPositive_of_coe_eq_smul hli (hfgC.finrank_eq_add hfC hgC).symm (mul_pos hc hd) ?_
  rw [hx', hy', smul_tmul_smul, map_smul, Submodule.coe_smul, coe_detLineShortExactEquiv_tmul,
    ιMulti_append_comp_complexToRealFamily]

end ShortExact

section FourTerm

variable {A B C D : Type*} [AddCommGroup A] [Module ℂ A] [Module ℝ A] [IsScalarTower ℝ ℂ A]
  [AddCommGroup B] [Module ℂ B] [Module ℝ B] [IsScalarTower ℝ ℂ B]
  [AddCommGroup C] [Module ℂ C] [Module ℝ C] [IsScalarTower ℝ ℂ C]
  [AddCommGroup D] [Module ℂ D] [Module ℝ D] [IsScalarTower ℝ ℂ D]
  -- Real finite-dimensionality follows from the complex one through the scalar tower, but
  -- `TauCeti.detLineFourTermEquiv` takes it as an instance argument.
  [FiniteDimensional ℝ A] [FiniteDimensional ℝ C]
  {f : A →ₗ[ℂ] B} {g : B →ₗ[ℂ] C} {h : C →ₗ[ℂ] D}

/-- **Four-term exact sequences respect complex orientations.** For an exact sequence
`0 → A → B → C → D → 0` of complex vector spaces and complex-linear maps, the identification
`det B ⊗ (det C)^* ≃ det A ⊗ (det D)^*` of real determinant lines (`TauCeti.detLineFourTermEquiv`)
sends complex positive elements to complex positive elements. For the exact sequence
`0 → ker D₁ → ker (D₁.coprod D₂) → Λ → coker D₁ → 0` of a complex stabilization of a complex-linear
operator `D₁`, this says that the complex orientation of `det (ker D₁) ⊗ (det (coker D₁))^*` is the
one induced by the complex orientations of the stabilized kernel and of the stabilizing space. -/
theorem isComplexPositiveTMulDual_detLineFourTermEquiv
    (hf : Function.Injective (f.restrictScalars ℝ))
    (hfg : Function.Exact (f.restrictScalars ℝ) (g.restrictScalars ℝ))
    (hgh : Function.Exact (g.restrictScalars ℝ) (h.restrictScalars ℝ))
    (hh : Function.Surjective (h.restrictScalars ℝ))
    {t : detLine ℝ B ⊗[ℝ] Dual ℝ (detLine ℝ C)} (ht : IsComplexPositiveTMulDual t) :
    IsComplexPositiveTMulDual (detLineFourTermEquiv hf hfg hgh hh t) := by
  -- The hypotheses on the real restrictions are the same statements about `f`, `g` and `h`.
  have hfC : Function.Injective f := hf
  have hfgC : Function.Exact f g := hfg
  have hghC : Function.Exact g h := hgh
  have hhC : Function.Surjective h := hh
  have : FiniteDimensional ℂ A := Module.Finite.of_restrictScalars_finite ℝ ℂ A
  have : FiniteDimensional ℂ C := Module.Finite.of_restrictScalars_finite ℝ ℂ C
  have : FiniteDimensional ℂ D := Module.Finite.of_surjective h hhC
  have : FiniteDimensional ℂ B := finiteDimensional_of_exact hfgC
  have : FiniteDimensional ℝ D := Module.Finite.trans ℂ D
  -- Complex bases of `A`, of `range g` and of `D`, and lifts of the last two to `B` and `C`.
  set bA := finBasis ℂ A
  set bR := finBasis ℂ (LinearMap.range g)
  set bD := finBasis ℂ D
  set v : Fin (finrank ℂ (LinearMap.range g)) → B := fun i ↦ (LinearMap.mem_range.1 (bR i).2).choose
  have hv : g.rangeRestrict ∘ v = bR :=
    funext fun i ↦ Subtype.ext (LinearMap.mem_range.1 (bR i).2).choose_spec
  have hv' : g ∘ v = (LinearMap.range g).subtype ∘ bR := by
    rw [← hv, ← Function.comp_assoc, ← LinearMap.coe_comp, LinearMap.subtype_comp_rangeRestrict]
  set z : Fin (finrank ℂ D) → C := Function.surjInv hhC ∘ bD
  have hz : h ∘ z = bD := funext fun i ↦ Function.surjInv_eq hhC _
  -- They give complex bases of `B` and of `C` adapted to the exact sequence.
  have hliB : LinearIndependent ℂ (Fin.append (f ∘ bA) v) :=
    hfgC.rangeRestrict.linearIndependent_append hfC bA.linearIndependent
      (hv ▸ bR.linearIndependent)
  have hliC : LinearIndependent ℂ (Fin.append (g ∘ v) z) := by
    rw [hv']
    exact hghC.range_subtype.linearIndependent_append (LinearMap.range g).injective_subtype
      bR.linearIndependent (hz ▸ bD.linearIndependent)
  have hB := hfgC.rangeRestrict.finrank_eq_add hfC g.surjective_rangeRestrict
  have hC := hghC.range_subtype.finrank_eq_add (LinearMap.range g).injective_subtype hhC
  -- Real dimensions are twice the complex ones.
  have hA₂ := finrank_real_eq_two_mul_finrank_complex (V := A)
  have hR₂ : finrank ℝ (LinearMap.range (g.restrictScalars ℝ)) =
      2 * finrank ℂ (LinearMap.range g) :=
    finrank_real_eq_two_mul_finrank_complex (V := (LinearMap.range g).restrictScalars ℝ)
  have hB₂ := finrank_real_eq_two_mul_finrank_complex (V := B)
  have hC₂ := finrank_real_eq_two_mul_finrank_complex (V := C)
  have hD₂ := finrank_real_eq_two_mul_finrank_complex (V := D)
  -- The real families entering `TauCeti.detLineFourTermEquiv_tmul_eq_smul_tmul`.
  set uR := complexToRealFamily ⇑bA ∘ Fin.cast hA₂
  set vR := complexToRealFamily v ∘ Fin.cast hR₂
  set zR := complexToRealFamily z ∘ Fin.cast hD₂
  set β : detLine ℝ B := exteriorPower.ιMulti ℝ _
    (Fin.append ((f.restrictScalars ℝ) ∘ uR) vR ∘ Fin.cast (by omega))
  set γ : detLine ℝ C := exteriorPower.ιMulti ℝ _
    (Fin.append ((g.restrictScalars ℝ) ∘ vR) zR ∘ Fin.cast (by omega))
  have hβ : (β : ExteriorAlgebra ℝ B) =
      ExteriorAlgebra.ιMulti ℝ _ (Fin.append ((f.restrictScalars ℝ) ∘ uR) vR) := by
    simp [β]
  have hγ : (γ : ExteriorAlgebra ℝ C) =
      ExteriorAlgebra.ιMulti ℝ _ (Fin.append ((g.restrictScalars ℝ) ∘ vR) zR) := by
    simp [γ]
  -- `β`, `γ` and the exterior product of the images of `zR` in `D` are complex positive.
  have hβpos : IsComplexPositive β := by
    refine isComplexPositive_of_coe_eq_smul hliB hB.symm one_pos ?_
    rw [hβ, one_smul]
    exact ιMulti_append_comp_complexToRealFamily f _ _ hA₂ hR₂
  have hγpos : IsComplexPositive γ := by
    refine isComplexPositive_of_coe_eq_smul hliC hC.symm one_pos ?_
    rw [hγ, one_smul]
    exact ιMulti_append_comp_complexToRealFamily g _ _ hR₂ hD₂
  have hδpos : IsComplexPositive
      (exteriorPower.ιMulti ℝ (finrank ℝ D) ((h.restrictScalars ℝ) ∘ zR)) :=
    ⟨finrank ℂ D, bD, 1, one_pos, by
      simp [zR, ← Function.comp_assoc, ← complexToRealFamily_comp, hz]⟩
  obtain ⟨ξ, hξ⟩ := Projective.exists_dual_eq_one ℝ hδpos.ne_zero
  -- Compute the image of `t = x ⊗ φ`, writing `x` as a positive multiple of `β`.
  obtain ⟨x, φ, hx, hφ, rfl⟩ := ht
  obtain ⟨c, hc, rfl⟩ := hβpos.exists_pos_smul_eq hx
  rw [← smul_tmul', map_smul, detLineFourTermEquiv_tmul_eq_smul_tmul hf hfg hgh hh uR vR zR hβ hγ φ
    hξ, smul_smul, smul_tmul']
  refine IsComplexPositive.isComplexPositiveTMulDual_tmul (IsComplexPositive.smul ?_
    (mul_pos hc (hφ γ hγpos))) (hδpos.isComplexPositiveDual_of_apply_eq_one hξ)
  exact ⟨finrank ℂ A, bA, 1, one_pos, by simp [uR]⟩

end FourTerm

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Complex.Orientation
public import TauCeti.LinearAlgebra.Determinant.Exact
import TauCeti.LinearAlgebra.Basis.Exact
import TauCeti.LinearAlgebra.Complex.Finrank
import TauCeti.LinearAlgebra.Dimension.FinrankOne
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.ExteriorPower.Basis
import TauCeti.LinearAlgebra.LinearEquiv.Basic

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
  (`TauCeti.isComplexPositiveTMulDual_detLineFourTermEquiv`), also when the sequence is
  isomorphic to the real restriction of a complex one through real isomorphisms of the first,
  second and fourth terms and the identity of the third
  (`TauCeti.isComplexPositiveTMulDual_detLineFourTermEquiv_of_congr`).

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

Complex-linear isomorphisms preserve complex positivity
(`TauCeti.isComplexPositive_detLineCongr_iff`). By contrast, a real-linear isomorphism `g`
anticommuting with `I`, that is, a conjugate-linear isomorphism, sends the pair `bᵢ, I • bᵢ` of a
complex basis `b` to `g bᵢ, -(I • g bᵢ)`, so it multiplies the complex orientation of `det E` by
`(-1) ^ n`, `n = finrank ℂ E` (`TauCeti.IsComplexPositive.neg_one_pow_smul_detLineCongr`);
likewise for `(det E)^*` and `det E ⊗ (det F)^*`.

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
* `TauCeti.isComplexPositive_detLineCongr_iff`,
  `TauCeti.isComplexPositiveDual_comp_detLineCongr_iff`,
  `TauCeti.isComplexPositiveTMulDual_congr_detLineCongr_iff`: complex positivity is invariant under
  the isomorphisms of determinant lines induced by complex-linear isomorphisms.
* `TauCeti.IsComplexPositive.neg_one_pow_smul_detLineCongr`,
  `TauCeti.IsComplexPositiveDual.neg_one_pow_smul_comp_detLineCongr`,
  `TauCeti.IsComplexPositiveTMulDual.neg_one_pow_smul_congr_detLineCongr`: conjugate-linear
  isomorphisms multiply complex orientations by `(-1)` to the complex dimension.
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
    simp [e, ← c.coe_complexToReal_reindex_complexRealIndexEquiv, Basis.det_reindex,
      Function.comp_assoc, Basis.det_complexToReal]
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

/-- An element of `det F` whose image in the exterior algebra is a positive multiple of the exterior
product of the image under a complex-linear map `f` of the real family underlying `u`, followed by
the real family underlying `v`, is complex positive when `(f ∘ u, v)` is a complex basis `bF`. This
is the complex positive element of the determinant line of the middle term of an exact sequence. -/
theorem isComplexPositive_of_coe_eq_smul_ιMulti_append {m a b : ℕ} (f : E →ₗ[ℂ] F)
    {u : Fin m → E} {v : Fin n → F} (bF : Basis (Fin (m + n)) ℂ F)
    (hbF : ⇑bF = Fin.append (f ∘ u) v) (ha : a = 2 * m) (hb : b = 2 * n) {x : detLine ℝ F}
    {c : ℝ} (hc : 0 < c) (hx : (x : ExteriorAlgebra ℝ F) = c • ExteriorAlgebra.ιMulti ℝ (a + b)
      (Fin.append ((f.restrictScalars ℝ) ∘ complexToRealFamily u ∘ Fin.cast ha)
        (complexToRealFamily v ∘ Fin.cast hb))) :
    IsComplexPositive x :=
  ⟨m + n, bF, c, hc, by rw [hx, ιMulti_append_comp_complexToRealFamily, hbF]⟩

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

omit [IsScalarTower ℝ ℂ E] in
/-- The exterior product `b₀ ∧ I • b₀ ∧ b₁ ∧ I • b₁ ∧ ⋯` of the real family underlying a complex
basis `b`, as an element of `det E`, is complex positive. -/
theorem isComplexPositive_ιMulti_complexToRealFamily (b : Basis (Fin n) ℂ E)
    (h : finrank ℝ E = 2 * n) :
    IsComplexPositive (exteriorPower.ιMulti ℝ _ (complexToRealFamily ⇑b ∘ Fin.cast h)) :=
  ⟨n, b, 1, one_pos, by simp⟩

/-- The exterior product of the image under a complex-linear map `f` of the real family underlying
a family `v` is complex positive in `det F` when `f ∘ v` is a complex basis `b` of `F`. -/
theorem isComplexPositive_ιMulti_comp_complexToRealFamily (f : E →ₗ[ℂ] F) {v : Fin n → E}
    (b : Basis (Fin n) ℂ F) (hv : f ∘ v = b) (h : finrank ℝ F = 2 * n) :
    IsComplexPositive
      (exteriorPower.ιMulti ℝ _ ((f.restrictScalars ℝ) ∘ complexToRealFamily v ∘ Fin.cast h)) := by
  rw [LinearMap.coe_restrictScalars, ← Function.comp_assoc, ← complexToRealFamily_comp, hv]
  exact isComplexPositive_ιMulti_complexToRealFamily b h

/-- Every finite-dimensional complex vector space has a complex positive element of its real
determinant line. -/
theorem exists_isComplexPositive [FiniteDimensional ℂ E] : ∃ x : detLine ℝ E, IsComplexPositive x :=
  ⟨_, isComplexPositive_ιMulti_complexToRealFamily (finBasis ℂ E)
    finrank_real_eq_two_mul_finrank_complex⟩

/-- Two complex positive elements of `det E` differ by a positive factor. -/
theorem IsComplexPositive.exists_pos_smul_eq (hx : IsComplexPositive x) (hy : IsComplexPositive y) :
    ∃ c : ℝ, 0 < c ∧ y = c • x := by
  obtain ⟨n, b, c, hc, hx⟩ := hx
  obtain ⟨d, hd, hy⟩ := (isComplexPositive_iff b).1 hy
  refine ⟨d / c, div_pos hd hc, Subtype.ext ?_⟩
  rw [Submodule.coe_smul, hx, hy, smul_smul, div_mul_cancel₀ _ hc.ne']

/-- The negative of a complex positive element is not complex positive: complex positivity is an
orientation of `det E`, not a vacuous condition. -/
theorem IsComplexPositive.not_neg (hx : IsComplexPositive x) : ¬ IsComplexPositive (-x) :=
  not_neg_of_exists_pos_smul_eq (fun _ ↦ ne_zero) (fun _ _ ↦ exists_pos_smul_eq) hx

/-- Exactly one of `x` and `-x` is complex positive for each nonzero element `x` of the line
`det E`; that at most one is follows from `TauCeti.IsComplexPositive.not_neg`. -/
theorem isComplexPositive_or_isComplexPositive_neg [FiniteDimensional ℂ E] (hx : x ≠ 0) :
    IsComplexPositive x ∨ IsComplexPositive (-x) := by
  have : Module.Finite ℝ E := Module.Finite.trans ℂ E
  obtain ⟨x₀, hx₀⟩ := exists_isComplexPositive (E := E)
  exact or_neg_of_finrank_eq_one (finrank_detLine ℝ E) (fun _ h _ ↦ h.smul) hx₀ hx₀.ne_zero hx

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

/-- Two complex positive functionals on `det E` differ by a positive factor. -/
theorem IsComplexPositiveDual.exists_pos_smul_eq [FiniteDimensional ℂ E]
    (hφ : IsComplexPositiveDual φ) (hψ : IsComplexPositiveDual ψ) :
    ∃ c : ℝ, 0 < c ∧ ψ = c • φ := by
  have : Module.Finite ℝ E := Module.Finite.trans ℂ E
  obtain ⟨x, hx⟩ := exists_isComplexPositive (E := E)
  exact exists_pos_smul_eq_of_apply_pos_of_finrank_eq_one (finrank_detLine ℝ E) (hφ x hx)
    (hψ x hx)

/-- The negative of a complex positive functional is not complex positive. -/
theorem IsComplexPositiveDual.not_neg [FiniteDimensional ℂ E] (hφ : IsComplexPositiveDual φ) :
    ¬ IsComplexPositiveDual (-φ) :=
  not_neg_of_exists_pos_smul_eq (fun _ ↦ ne_zero) (fun _ _ ↦ exists_pos_smul_eq) hφ

/-- Exactly one of `φ` and `-φ` is complex positive for each nonzero functional `φ` on `det E`;
that at most one is follows from `TauCeti.IsComplexPositiveDual.not_neg`. -/
theorem isComplexPositiveDual_or_isComplexPositiveDual_neg [FiniteDimensional ℂ E] (hφ : φ ≠ 0) :
    IsComplexPositiveDual φ ∨ IsComplexPositiveDual (-φ) := by
  have : Module.Finite ℝ E := Module.Finite.trans ℂ E
  obtain ⟨φ₀, hφ₀⟩ := exists_isComplexPositiveDual (E := E)
  exact or_neg_of_finrank_eq_one (by rw [Subspace.dual_finrank_eq, finrank_detLine])
    (fun _ h _ ↦ h.smul) hφ₀ hφ₀.ne_zero hφ

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
    (ht : IsComplexPositiveTMulDual t) : ¬ IsComplexPositiveTMulDual (-t) :=
  not_neg_of_exists_pos_smul_eq (fun _ ↦ ne_zero) (fun _ _ ↦ exists_pos_smul_eq) ht

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
  exact or_neg_of_finrank_eq_one hrank (fun _ h _ ↦ h.smul) ht₀ ht₀.ne_zero ht

end TMulDual

/-! ### Transport along complex-linear isomorphisms -/

section Congr

variable {E' F' : Type*} [AddCommGroup E'] [Module ℂ E'] [Module ℝ E'] [IsScalarTower ℝ ℂ E']
  [AddCommGroup F'] [Module ℂ F'] [Module ℝ F'] [IsScalarTower ℝ ℂ F']

/-- The isomorphism of real determinant lines induced by a complex-linear isomorphism maps complex
positive elements to complex positive elements. -/
theorem IsComplexPositive.detLineCongr {x : detLine ℝ E} (hx : IsComplexPositive x)
    (e : E ≃ₗ[ℂ] F) : IsComplexPositive (LinearEquiv.detLineCongr (e.restrictScalars ℝ) x) := by
  obtain ⟨n, b, c, hc, hx⟩ := hx
  refine ⟨n, b.map e, c, hc, ?_⟩
  rw [Basis.coe_map, ← e.coe_toLinearMap, complexToRealFamily_comp]
  simp [hx]

/-- **Complex positivity is invariant under complex-linear isomorphisms**: the isomorphism of real
determinant lines induced by a complex-linear isomorphism `e` maps an element to a complex positive
element exactly when the element is complex positive. -/
@[simp]
theorem isComplexPositive_detLineCongr_iff (e : E ≃ₗ[ℂ] F) {x : detLine ℝ E} :
    IsComplexPositive (LinearEquiv.detLineCongr (e.restrictScalars ℝ) x) ↔ IsComplexPositive x := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.detLineCongr e⟩
  simpa only [← LinearEquiv.symm_restrictScalars, ← LinearEquiv.detLineCongr_symm,
    LinearEquiv.symm_apply_apply] using h.detLineCongr e.symm

/-- Pulling a functional back along the isomorphism of real determinant lines induced by a
complex-linear isomorphism preserves and reflects complex positivity. -/
@[simp]
theorem isComplexPositiveDual_comp_detLineCongr_iff (e : E ≃ₗ[ℂ] F)
    {φ : Dual ℝ (detLine ℝ F)} :
    IsComplexPositiveDual (φ ∘ₗ (LinearEquiv.detLineCongr (e.restrictScalars ℝ)).toLinearMap) ↔
      IsComplexPositiveDual φ := by
  refine ⟨fun hφ y hy ↦ ?_, fun hφ x hx ↦ hφ _ (hx.detLineCongr e)⟩
  obtain ⟨x, rfl⟩ := (LinearEquiv.detLineCongr (e.restrictScalars ℝ)).surjective y
  exact hφ x ((isComplexPositive_detLineCongr_iff e).1 hy)

/-- The isomorphism `det E ⊗ (det F)^* ≃ det E' ⊗ (det F')^*` induced by complex-linear
isomorphisms `e₁ : E ≃ E'` and `e₂ : F ≃ F'`, the shape of `LinearMap.detLineCongr`, maps complex
positive elements to complex positive elements. -/
theorem IsComplexPositiveTMulDual.congr_detLineCongr {t : detLine ℝ E ⊗[ℝ] Dual ℝ (detLine ℝ F)}
    (ht : IsComplexPositiveTMulDual t) (e₁ : E ≃ₗ[ℂ] E') (e₂ : F ≃ₗ[ℂ] F') :
    IsComplexPositiveTMulDual (TensorProduct.congr
      (LinearEquiv.detLineCongr (e₁.restrictScalars ℝ))
      (LinearEquiv.detLineCongr (e₂.restrictScalars ℝ)).symm.dualMap t) := by
  obtain ⟨x, φ, hx, hφ, rfl⟩ := ht
  refine ⟨_, _, hx.detLineCongr e₁, ?_, TensorProduct.congr_tmul _ _ _ _⟩
  -- The second factor is `φ` pulled back along the isomorphism induced by `e₂.symm`.
  have hφ' : (LinearEquiv.detLineCongr (e₂.restrictScalars ℝ)).symm.dualMap φ =
      φ ∘ₗ (LinearEquiv.detLineCongr (e₂.symm.restrictScalars ℝ)).toLinearMap :=
    LinearMap.ext fun _ ↦ by simp [LinearEquiv.detLineCongr_symm]
  rw [hφ']
  exact (isComplexPositiveDual_comp_detLineCongr_iff e₂.symm).2 hφ

/-- **Complex positivity of `det E ⊗ (det F)^*` is invariant under complex-linear isomorphisms**:
the isomorphism `det E ⊗ (det F)^* ≃ det E' ⊗ (det F')^*` induced by complex-linear isomorphisms
`e₁ : E ≃ E'` and `e₂ : F ≃ F'` maps an element to a complex positive element exactly when the
element is complex positive. The second factor is stated in simp normal form, the dual of the
isomorphism induced by `e₂.symm`. -/
@[simp]
theorem isComplexPositiveTMulDual_congr_detLineCongr_iff (e₁ : E ≃ₗ[ℂ] E') (e₂ : F ≃ₗ[ℂ] F')
    {t : detLine ℝ E ⊗[ℝ] Dual ℝ (detLine ℝ F)} :
    IsComplexPositiveTMulDual (TensorProduct.congr
        (LinearEquiv.detLineCongr (e₁.restrictScalars ℝ))
        (LinearEquiv.detLineCongr (e₂.symm.restrictScalars ℝ)).dualMap t) ↔
      IsComplexPositiveTMulDual t := by
  rw [← LinearEquiv.symm_restrictScalars, ← LinearEquiv.detLineCongr_symm]
  refine ⟨fun h ↦ ?_, fun h ↦ h.congr_detLineCongr e₁ e₂⟩
  simpa only [← LinearEquiv.symm_restrictScalars, ← LinearEquiv.detLineCongr_symm,
    ← LinearEquiv.dualMap_symm, ← TensorProduct.congr_symm, LinearEquiv.symm_apply_apply]
    using h.congr_detLineCongr e₁.symm e₂.symm

end Congr

/-! ### Transport along conjugate-linear isomorphisms -/

section Conj

variable {n : ℕ}

omit [IsScalarTower ℝ ℂ E] [IsScalarTower ℝ ℂ F] in
/-- A real-linear map anticommuting with `I` maps the real family `(v₀, I • v₀, v₁, …)` underlying
`v` to that underlying `g ∘ v` with every second vector negated, so it maps the exterior product of
the first to `(-1) ^ n` times that of the second. -/
private theorem map_ιMulti_complexToRealFamily_of_map_I_smul (g : E →ₗ[ℝ] F)
    (hg : ∀ x, g (Complex.I • x) = -(Complex.I • g x)) (v : Fin n → E) :
    ExteriorAlgebra.map g (ExteriorAlgebra.ιMulti ℝ (2 * n) (complexToRealFamily v)) =
      (-1 : ℝ) ^ n • ExteriorAlgebra.ιMulti ℝ (2 * n) (complexToRealFamily (g ∘ v)) := by
  set s : Fin (2 * n) → ℝ := fun j ↦ if ((complexRealIndexEquiv n).symm j).2 = 0 then 1 else -1
  have hv : g ∘ complexToRealFamily v = fun j ↦ s j • complexToRealFamily (g ∘ v) j := by
    funext j
    obtain ⟨⟨i, k⟩, rfl⟩ := (complexRealIndexEquiv n).surjective j
    fin_cases k <;> simp [s, hg]
  have hs : ∏ j, s j = (-1) ^ n := by
    rw [← (complexRealIndexEquiv n).prod_comp, Fintype.prod_prod_type]
    simp [s, Fin.prod_univ_two]
  rw [ExteriorAlgebra.map_apply_ιMulti, hv, AlternatingMap.map_smul_univ, hs]

/-- **A conjugate-linear isomorphism reverses the complex orientation `(-1) ^ n` times**: the
isomorphism of real determinant lines induced by a real-linear isomorphism `g` anticommuting with
`I` maps a complex positive element to `(-1) ^ n` times a complex positive element,
`n = finrank ℂ E`. -/
theorem IsComplexPositive.neg_one_pow_smul_detLineCongr [FiniteDimensional ℂ E]
    {x : detLine ℝ E} (hx : IsComplexPositive x) (g : E ≃ₗ[ℝ] F)
    (hg : ∀ x, g (Complex.I • x) = -(Complex.I • g x)) :
    IsComplexPositive ((-1 : ℝ) ^ finrank ℂ E • LinearEquiv.detLineCongr g x) := by
  set b := finBasis ℂ E
  obtain ⟨c, hc, hx⟩ := (isComplexPositive_iff b).1 hx
  obtain ⟨b', hb'⟩ := g.exists_basis_coe_eq_comp_of_map_I_smul hg b
  refine (isComplexPositive_iff b').2 ⟨c, hc, ?_⟩
  have hmap := map_ιMulti_complexToRealFamily_of_map_I_smul g.toLinearMap hg b
  rw [LinearEquiv.coe_coe, ← hb'] at hmap
  rw [Submodule.coe_smul, LinearEquiv.coe_detLineCongr, hx, map_smul, hmap, smul_comm c, smul_smul,
    ← mul_pow]
  simp

/-- Pulling a complex positive functional back along the isomorphism of real determinant lines
induced by a conjugate-linear isomorphism `g` gives `(-1) ^ n` times a complex positive functional,
`n = finrank ℂ F`. -/
theorem IsComplexPositiveDual.neg_one_pow_smul_comp_detLineCongr [FiniteDimensional ℂ F]
    {φ : Dual ℝ (detLine ℝ E)} (hφ : IsComplexPositiveDual φ) (g : F ≃ₗ[ℝ] E)
    (hg : ∀ x, g (Complex.I • x) = -(Complex.I • g x)) :
    IsComplexPositiveDual
      ((-1 : ℝ) ^ finrank ℂ F • φ ∘ₗ (LinearEquiv.detLineCongr g).toLinearMap) := by
  obtain ⟨y, hy⟩ := exists_isComplexPositive (E := F)
  rw [hy.isComplexPositiveDual_iff, LinearMap.smul_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, ← map_smul]
  exact (hy.neg_one_pow_smul_detLineCongr g hg).isComplexPositiveDual_iff.1 hφ

/-- The isomorphism `det E ⊗ (det F)^* ≃ det E' ⊗ (det F')^*` induced by conjugate-linear
isomorphisms `e₁ : E ≃ E'` and `e₂ : F ≃ F'`, the shape of `LinearMap.detLineCongr`, maps a
complex positive element to `(-1) ^ (m + n)` times a complex positive element, where `m` and `n`
are the complex dimensions of `E` and `F`. -/
theorem IsComplexPositiveTMulDual.neg_one_pow_smul_congr_detLineCongr {E' F' : Type*}
    [AddCommGroup E'] [Module ℂ E'] [Module ℝ E'] [IsScalarTower ℝ ℂ E']
    [AddCommGroup F'] [Module ℂ F'] [Module ℝ F'] [IsScalarTower ℝ ℂ F']
    [FiniteDimensional ℂ E] [FiniteDimensional ℂ F] {t : detLine ℝ E ⊗[ℝ] Dual ℝ (detLine ℝ F)}
    (ht : IsComplexPositiveTMulDual t) (e₁ : E ≃ₗ[ℝ] E') (e₂ : F ≃ₗ[ℝ] F')
    (he₁ : ∀ x, e₁ (Complex.I • x) = -(Complex.I • e₁ x))
    (he₂ : ∀ y, e₂ (Complex.I • y) = -(Complex.I • e₂ y)) :
    IsComplexPositiveTMulDual ((-1 : ℝ) ^ (finrank ℂ E + finrank ℂ F) •
      TensorProduct.congr (LinearEquiv.detLineCongr e₁)
        (LinearEquiv.detLineCongr e₂).symm.dualMap t) := by
  have := e₂.finiteDimensional_complex
  obtain ⟨x, hx⟩ := exists_isComplexPositive (E := E)
  obtain ⟨φ, hφ⟩ := exists_isComplexPositiveDual (E := F)
  obtain ⟨c, hc, rfl⟩ := (hx.isComplexPositiveTMulDual_tmul hφ).exists_pos_smul_eq ht
  have he₂' (y : F') : e₂.symm (Complex.I • y) = -(Complex.I • e₂.symm y) := by
    rw [LinearEquiv.symm_apply_eq, map_neg, he₂, LinearEquiv.apply_symm_apply, neg_neg]
  have hφ' := hφ.neg_one_pow_smul_comp_detLineCongr e₂.symm he₂'
  rw [e₂.symm.finrank_complex_eq, ← LinearEquiv.detLineCongr_symm] at hφ'
  rw [map_smul, smul_comm, TensorProduct.congr_tmul, pow_add, ← smul_tmul_smul]
  exact ((hx.neg_one_pow_smul_detLineCongr e₁ he₁).isComplexPositiveTMulDual_tmul hφ').smul hc

end Conj

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
  -- Lift a basis of `W` to `V`; with the image of a basis of `U` it is a basis of `V`.
  obtain ⟨v, bV, hv, hbV⟩ := Basis.exists_coe_eq_append_lift hfC hfgC hgC (finBasis ℂ U)
    (finBasis ℂ W)
  have hU := finrank_real_eq_two_mul_finrank_complex (V := U)
  have hW := finrank_real_eq_two_mul_finrank_complex (V := W)
  -- Write `x` and `y` as positive multiples of exterior products of real families.
  obtain ⟨c, hc, rfl⟩ :=
    (isComplexPositive_ιMulti_complexToRealFamily (finBasis ℂ U) hU).exists_pos_smul_eq hx
  obtain ⟨d, hd, rfl⟩ :=
    (isComplexPositive_ιMulti_comp_complexToRealFamily g (finBasis ℂ W) hv hW).exists_pos_smul_eq hy
  refine isComplexPositive_of_coe_eq_smul_ιMulti_append f bV hbV hU hW (mul_pos hc hd) ?_
  rw [smul_tmul_smul, map_smul, Submodule.coe_smul, coe_detLineShortExactEquiv_tmul]

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
  -- Complex bases of `A`, of `range g` and of `D`, lifts of the last two to `B` and `C`, and the
  -- complex bases of `B` and of `C` they give, adapted to the exact sequence.
  set bA := finBasis ℂ A
  set bR := finBasis ℂ (LinearMap.range g)
  set bD := finBasis ℂ D
  obtain ⟨v, bB, hv, hbB⟩ := Basis.exists_coe_eq_append_lift hfC hfgC.rangeRestrict
    g.surjective_rangeRestrict bA bR
  obtain ⟨z, bC, hz, hbC⟩ := Basis.exists_coe_eq_append_lift (LinearMap.range g).injective_subtype
    hghC.range_subtype hhC bR bD
  have hv' : g ∘ v = (LinearMap.range g).subtype ∘ bR := by
    rw [← hv, ← Function.comp_assoc, ← LinearMap.coe_comp, LinearMap.subtype_comp_rangeRestrict]
  rw [← hv'] at hbC
  have hB : finrank ℂ B = _ := (finrank_eq_card_basis bB).trans (Fintype.card_fin _)
  have hC : finrank ℂ C = _ := (finrank_eq_card_basis bC).trans (Fintype.card_fin _)
  -- Real dimensions are twice the complex ones.
  have hA₂ := finrank_real_eq_two_mul_finrank_complex (V := A)
  have hR₂ : finrank ℝ (LinearMap.range (g.restrictScalars ℝ)) =
      2 * finrank ℂ (LinearMap.range g) := by
    rw [LinearMap.range_restrictScalars]
    exact finrank_real_eq_two_mul_finrank_complex (V := (LinearMap.range g).restrictScalars ℝ)
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
  have hβpos : IsComplexPositive β :=
    isComplexPositive_of_coe_eq_smul_ιMulti_append f bB hbB hA₂ hR₂ one_pos (by rw [hβ, one_smul])
  have hγpos : IsComplexPositive γ :=
    isComplexPositive_of_coe_eq_smul_ιMulti_append g bC hbC hR₂ hD₂ one_pos
      (by rw [hγ, one_smul])
  have hδpos : IsComplexPositive
      (exteriorPower.ιMulti ℝ (finrank ℝ D) ((h.restrictScalars ℝ) ∘ zR)) :=
    isComplexPositive_ιMulti_comp_complexToRealFamily h bD hz hD₂
  obtain ⟨ξ, hξ⟩ := Projective.exists_dual_eq_one ℝ hδpos.ne_zero
  -- Compute the image of `t = x ⊗ φ`, writing `x` as a positive multiple of `β`.
  obtain ⟨x, φ, hx, hφ, rfl⟩ := ht
  obtain ⟨c, hc, rfl⟩ := hβpos.exists_pos_smul_eq hx
  rw [← smul_tmul', map_smul, detLineFourTermEquiv_tmul_eq_smul_tmul hf hfg hgh hh uR vR zR hβ hγ φ
    hξ, smul_smul, smul_tmul']
  refine IsComplexPositive.isComplexPositiveTMulDual_tmul (IsComplexPositive.smul ?_
    (mul_pos hc (hφ γ hγpos))) (hδpos.isComplexPositiveDual_of_apply_eq_one hξ)
  exact isComplexPositive_ιMulti_complexToRealFamily bA hA₂

/-- **Four-term exact sequences isomorphic to complex ones respect complex orientations.** Let
`0 → A' → B' → C → D' → 0` be an exact sequence of real vector spaces, isomorphic through real
isomorphisms `eA`, `eB` and `eD`, and the identity of `C`, to the real restriction of an exact
sequence `0 → A → B → C → D → 0` of complex vector spaces and complex-linear maps. Then the
identification `det B' ⊗ (det C)^* ≃ det A' ⊗ (det D')^*` (`TauCeti.detLineFourTermEquiv`) sends
the image of a complex positive element of `det B ⊗ (det C)^*` to the image of a complex positive
element of `det A ⊗ (det D)^*`. This is how complex orientations pass to sequences, such as the
kernel sequence of a stabilized Fredholm operator, whose terms are formed with real scalars. -/
theorem isComplexPositiveTMulDual_detLineFourTermEquiv_of_congr
    (hf : Function.Injective (f.restrictScalars ℝ))
    (hfg : Function.Exact (f.restrictScalars ℝ) (g.restrictScalars ℝ))
    (hgh : Function.Exact (g.restrictScalars ℝ) (h.restrictScalars ℝ))
    (hh : Function.Surjective (h.restrictScalars ℝ))
    {A' B' D' : Type*} [AddCommGroup A'] [Module ℝ A'] [AddCommGroup B'] [Module ℝ B']
    [AddCommGroup D'] [Module ℝ D'] [FiniteDimensional ℝ A'] {f' : A' →ₗ[ℝ] B'}
    {g' : B' →ₗ[ℝ] C} {h' : C →ₗ[ℝ] D'} (hf' : Function.Injective f')
    (hfg' : Function.Exact f' g') (hgh' : Function.Exact g' h') (hh' : Function.Surjective h')
    (eA : A ≃ₗ[ℝ] A') (eB : B ≃ₗ[ℝ] B') (eD : D ≃ₗ[ℝ] D')
    (hfA : f' ∘ₗ eA.toLinearMap = eB.toLinearMap ∘ₗ f.restrictScalars ℝ)
    (hgB : g' ∘ₗ eB.toLinearMap = g.restrictScalars ℝ)
    (hhD : h' = eD.toLinearMap ∘ₗ h.restrictScalars ℝ)
    {t : detLine ℝ B ⊗[ℝ] Dual ℝ (detLine ℝ C)} (ht : IsComplexPositiveTMulDual t) :
    IsComplexPositiveTMulDual (TensorProduct.congr eA.symm.detLineCongr eD.detLineCongr.dualMap
      (detLineFourTermEquiv hf' hfg' hgh' hh' (LinearEquiv.rTensor _ eB.detLineCongr t))) := by
  have key := detLineFourTermEquiv_congr hf hfg hgh hh hf' hfg' hgh' hh' eA eB
    (LinearEquiv.refl ℝ C) eD hfA (by rw [hgB, LinearEquiv.refl_toLinearMap, LinearMap.id_comp])
    (by rw [hhD, LinearEquiv.refl_toLinearMap, LinearMap.comp_id]) t
  have hX : LinearEquiv.rTensor _ eB.detLineCongr = TensorProduct.congr eB.detLineCongr
      (LinearEquiv.refl ℝ C).detLineCongr.symm.dualMap := by
    rw [LinearEquiv.detLineCongr_refl, LinearEquiv.refl_symm, LinearEquiv.dualMap_refl,
      LinearEquiv.rTensor]
  rw [hX, key, TensorProduct.congr_congr, ← LinearEquiv.detLineCongr_symm,
    ← LinearEquiv.dualMap_symm, LinearEquiv.self_trans_symm, LinearEquiv.symm_trans_self,
    TensorProduct.congr_refl_refl, LinearEquiv.refl_apply]
  exact isComplexPositiveTMulDual_detLineFourTermEquiv hf hfg hgh hh ht

end FourTerm

end TauCeti

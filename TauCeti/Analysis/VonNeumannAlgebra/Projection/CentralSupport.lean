/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.VonNeumannAlgebra.Lattice
public import TauCeti.Analysis.VonNeumannAlgebra.Projection.Basic
import Mathlib.Algebra.Order.Star.Projection
import TauCeti.Analysis.VonNeumannAlgebra.Density
import TauCeti.Topology.Algebra.Module.ClosedSubmodule
import TauCeti.Topology.Algebra.Module.ContinuousLinearMap.IdempotentRange

/-!
# Central support in von Neumann algebras

In the center `M ⊓ M.commutant` of a concrete von Neumann algebra `M`, the **central support**
`M.centralSupport a` of an operator `a : H →L[ℂ] H` is the smallest central projection `z`
satisfying `z * a = a` (`VonNeumannAlgebra.centralSupportProjection`,
`VonNeumannAlgebra.centralSupport`). For `a ∈ M`, we identify `M.centralSupport a` geometrically
as the orthogonal projection onto the closed span of `{x (a ξ) | x ∈ M, ξ ∈ H}`
(`VonNeumannAlgebra.centralSupport_eq_starProjection_closure_span`) and deduce the
**central-support kernel theorem**
(`VonNeumannAlgebra.commutant_mul_eq_zero_iff_mul_centralSupport_eq_zero`): for every
`y ∈ M.commutant`, `y * a = 0 ↔ y * M.centralSupport a = 0`.

## Main declarations

* `VonNeumannAlgebra.centralSupportProjection`, `VonNeumannAlgebra.centralSupport`: central support
  of an operator relative to `M`.
* `VonNeumannAlgebra.centralSupportProjection_le_iff`, `VonNeumannAlgebra.centralSupport_le_iff`,
  `VonNeumannAlgebra.galoisConnection_centralSupportProjection`: universal property and adjunction
  of central support.
* `VonNeumannAlgebra.centralSupport_unitary_conj`: invariance under conjugation by unitaries in `M`.
* `VonNeumannAlgebra.centralSupport_eq_starProjection_closure_span`: geometric span formula.
* `VonNeumannAlgebra.commutant_mul_eq_zero_iff_mul_centralSupport_eq_zero`: central-support kernel
  theorem.

## References

* R. V. Kadison, J. R. Ringrose, *Fundamentals of the Theory of Operator Algebras I*,
  §5.5 and Proposition 5.5.2.
* M. Takesaki, *Theory of Operator Algebras I*, Proposition V.1.6.
-/

public section

namespace VonNeumannAlgebra

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The **central support** of `a : H →L[ℂ] H` relative to `M`, bundled as a projection in the
center `M ⊓ M.commutant`: the smallest central projection `z` satisfying `z * a = a`. -/
noncomputable def centralSupportProjection (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    (M ⊓ M.commutant).Projection :=
  sInf {z : (M ⊓ M.commutant).Projection | (z : H →L[ℂ] H) * a = a}

/-- The **central support** (or central carrier) `M.centralSupport a` of `a : H →L[ℂ] H` in `M`:
the smallest star projection in the center `M ⊓ M.commutant` fixing `a` on the left. -/
noncomputable def centralSupport (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) : H →L[ℂ] H :=
  M.centralSupportProjection a

@[simp]
theorem coe_centralSupportProjection (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    (M.centralSupportProjection a : H →L[ℂ] H) = M.centralSupport a :=
  (rfl)

theorem isStarProjection_centralSupport (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    IsStarProjection (M.centralSupport a) :=
  (M.centralSupportProjection a).isStarProjection

theorem centralSupport_mem (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    M.centralSupport a ∈ M :=
  (mem_inf.1 (M.centralSupportProjection a).coe_mem).1

theorem centralSupport_mem_commutant (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    M.centralSupport a ∈ M.commutant :=
  (mem_inf.1 (M.centralSupportProjection a).coe_mem).2

@[simp]
theorem centralSupport_mul_self (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) :
    M.centralSupport a * a = a := by
  rw [← coe_centralSupportProjection, Projection.mul_eq_right_iff_closure_range_le,
    centralSupportProjection, Projection.closedRange_sInf]
  exact le_sInf (Set.forall_mem_image.2 fun z hz =>
    (Projection.mul_eq_right_iff_closure_range_le z a).1 hz)

theorem mul_centralSupport_self {M : VonNeumannAlgebra H} {a : H →L[ℂ] H} (ha : a ∈ M) :
    a * M.centralSupport a = a := by
  rw [mem_commutant_iff.1 (M.centralSupport_mem_commutant a) a ha,
    M.centralSupport_mul_self a]

/-- Universal property of `M.centralSupportProjection`: a central projection `z` lies above
`M.centralSupportProjection a` if and only if `z * a = a`. -/
theorem centralSupportProjection_le_iff {M : VonNeumannAlgebra H} {a : H →L[ℂ] H}
    {z : (M ⊓ M.commutant).Projection} :
    M.centralSupportProjection a ≤ z ↔ (z : H →L[ℂ] H) * a = a :=
  ⟨fun h => (Projection.mul_eq_right_iff_closure_range_le z a).2 <|
      ((Projection.mul_eq_right_iff_closure_range_le (M.centralSupportProjection a) a).1
        (M.centralSupport_mul_self a)).trans (Projection.le_iff_closedRange_le.1 h),
    fun hz => sInf_le hz⟩

/-- Bundled central support is left adjoint to the inclusion of central projections into
`M.Projection`. -/
theorem galoisConnection_centralSupportProjection (M : VonNeumannAlgebra H) :
    GaloisConnection (fun p : M.Projection => M.centralSupportProjection p)
      (Projection.inclusion (inf_le_left : M ⊓ M.commutant ≤ M)) := by
  intro p z
  rw [centralSupportProjection_le_iff, Projection.le_iff_mul_eq_right, Projection.coe_inclusion]

/-- Universal property of `M.centralSupport`: for a central projection `z` of `M`,
`M.centralSupport a ≤ z ↔ z * a = a`. -/
theorem centralSupport_le_iff {M : VonNeumannAlgebra H} {a z : H →L[ℂ] H}
    (hz : IsStarProjection z) (hzM : z ∈ M) (hzC : z ∈ M.commutant) :
    M.centralSupport a ≤ z ↔ z * a = a := by
  rw [← coe_centralSupportProjection,
    ← Projection.coe_mk z hz (mem_inf.2 ⟨hzM, hzC⟩), Projection.coe_le_coe]
  exact centralSupportProjection_le_iff

/-- Bundled central support is monotone with respect to range inclusion. -/
theorem centralSupportProjection_mono_of_range_le {M : VonNeumannAlgebra H} {a b : H →L[ℂ] H}
    (h : a.range ≤ b.range) :
    M.centralSupportProjection a ≤ M.centralSupportProjection b := by
  rw [centralSupportProjection_le_iff, Projection.mul_eq_right_iff_closure_range_le]
  exact Submodule.closure_le.2 <| h.trans <| Submodule.closure_le.1 <|
    (Projection.mul_eq_right_iff_closure_range_le (M.centralSupportProjection b) b).1
      (M.centralSupport_mul_self b)

/-- Central support is monotone with respect to range inclusion. -/
theorem centralSupport_mono_of_range_le {M : VonNeumannAlgebra H} {a b : H →L[ℂ] H}
    (h : a.range ≤ b.range) :
    M.centralSupport a ≤ M.centralSupport b := by
  rw [← coe_centralSupportProjection, ← coe_centralSupportProjection, Projection.coe_le_coe]
  exact centralSupportProjection_mono_of_range_le h

/-- Bundled central support is monotone on `M.Projection`. -/
theorem centralSupportProjection_mono {M : VonNeumannAlgebra H} {p q : M.Projection}
    (h : p ≤ q) :
    M.centralSupportProjection p ≤ M.centralSupportProjection q :=
  centralSupportProjection_mono_of_range_le (Projection.le_iff_range_le.1 h)

/-- Central support is monotone on `M.Projection`. -/
theorem centralSupport_mono {M : VonNeumannAlgebra H} {p q : M.Projection} (h : p ≤ q) :
    M.centralSupport p ≤ M.centralSupport q :=
  centralSupport_mono_of_range_le (Projection.le_iff_range_le.1 h)

/-- Every star projection is bounded above by its central support. -/
theorem le_centralSupport {M : VonNeumannAlgebra H} {p : H →L[ℂ] H} (hp : IsStarProjection p) :
    p ≤ M.centralSupport p :=
  (hp.le_iff_mul_eq_right (M.isStarProjection_centralSupport p)).2 (M.centralSupport_mul_self p)

/-- A central projection is equal to its own central support. -/
theorem centralSupport_eq_self_of_mem_commutant {M : VonNeumannAlgebra H} {z : H →L[ℂ] H}
    (hz : IsStarProjection z) (hzM : z ∈ M) (hzC : z ∈ M.commutant) :
    M.centralSupport z = z :=
  le_antisymm ((centralSupport_le_iff hz hzM hzC).2 hz.isIdempotentElem.eq) (le_centralSupport hz)

@[simp]
theorem centralSupport_zero (M : VonNeumannAlgebra H) : M.centralSupport 0 = 0 :=
  le_antisymm
    ((centralSupport_le_iff (.zero _) (zero_mem M) (zero_mem M.commutant)).2 (zero_mul 0))
    (M.isStarProjection_centralSupport 0).nonneg

@[simp]
theorem centralSupportProjection_zero (M : VonNeumannAlgebra H) :
    M.centralSupportProjection 0 = ⊥ :=
  Projection.coe_inj.1 (by simp)

/-- The bundled central support of an operator vanishes if and only if the operator is zero. -/
@[simp]
theorem centralSupportProjection_eq_bot_iff {M : VonNeumannAlgebra H} {a : H →L[ℂ] H} :
    M.centralSupportProjection a = ⊥ ↔ a = 0 := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h0 : M.centralSupport a = 0 := by
      rw [← coe_centralSupportProjection, h, Projection.coe_bot]
    rw [← M.centralSupport_mul_self a, h0, zero_mul]
  · subst h
    exact centralSupportProjection_zero M

/-- The central support of an operator vanishes if and only if the operator is zero. -/
@[simp]
theorem centralSupport_eq_zero_iff {M : VonNeumannAlgebra H} {a : H →L[ℂ] H} :
    M.centralSupport a = 0 ↔ a = 0 :=
  ⟨fun h => by rw [← M.centralSupport_mul_self a, h, zero_mul], fun h => by simp [h]⟩

@[simp]
theorem centralSupport_one (M : VonNeumannAlgebra H) : M.centralSupport 1 = 1 :=
  centralSupport_eq_self_of_mem_commutant (.one _) (one_mem M) (one_mem M.commutant)

@[simp]
theorem centralSupportProjection_one (M : VonNeumannAlgebra H) :
    M.centralSupportProjection 1 = ⊤ :=
  Projection.coe_inj.1 (by simp)

/-- Conjugating an operator by a unitary in `M` preserves its bundled central support. -/
@[simp]
theorem centralSupportProjection_unitary_conj {M : VonNeumannAlgebra H} {u a : H →L[ℂ] H}
    (huM : u ∈ M) (hu : u ∈ unitary (H →L[ℂ] H)) :
    M.centralSupportProjection (u * a * star u) = M.centralSupportProjection a := by
  unfold centralSupportProjection
  congr 1
  ext z
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  set Φ := Unitary.conjStarAlgAut ℂ (H →L[ℂ] H) ⟨u, hu⟩
  have hzu : (z : H →L[ℂ] H) * u = u * z :=
    (mem_commutant_iff.1 (mem_inf.1 z.coe_mem).2 u huM).symm
  have hz : Φ z = z := by
    rw [Unitary.conjStarAlgAut_apply, ← hzu, mul_assoc, hu.2, mul_one]
  rw [← Unitary.conjStarAlgAut_apply (S := ℂ) ⟨u, hu⟩ a]
  calc (z : H →L[ℂ] H) * Φ a = Φ a
      ↔ Φ ((z : H →L[ℂ] H) * a) = Φ a := by rw [map_mul, hz]
    _ ↔ (z : H →L[ℂ] H) * a = a := Φ.injective.eq_iff

/-- Conjugating an operator by a unitary in `M` preserves its central support. -/
@[simp]
theorem centralSupport_unitary_conj {M : VonNeumannAlgebra H} {u a : H →L[ℂ] H}
    (huM : u ∈ M) (hu : u ∈ unitary (H →L[ℂ] H)) :
    M.centralSupport (u * a * star u) = M.centralSupport a :=
  congrArg Projection.val (M.centralSupportProjection_unitary_conj huM hu)

/-- The linear span of the `M`-orbits `{x (a ξ) | x ∈ M, ξ ∈ H}`. -/
private def orbitSpan (M : VonNeumannAlgebra H) (a : H →L[ℂ] H) : Submodule ℂ H :=
  Submodule.span ℂ {η : H | ∃ x ∈ M, ∃ ξ : H, x (a ξ) = η}

/-- For `a ∈ M`, `orbitSpan M a` is invariant under every operator in `M.commutant`. -/
private theorem orbitSpan_mem_invtSubmodule_commutant {M : VonNeumannAlgebra H}
    {a y : H →L[ℂ] H} (ha : a ∈ M) (hy : y ∈ M.commutant) :
    orbitSpan M a ∈ Module.End.invtSubmodule y := by
  rw [Module.End.mem_invtSubmodule, orbitSpan, Submodule.span_le]
  rintro _ ⟨x, hx, ξ, rfl⟩
  refine Submodule.subset_span ⟨x, hx, y ξ, ?_⟩
  have hcomm : y * (x * a) = (x * a) * y :=
    (mem_commutant_iff.1 hy (x * a) (mul_mem hx ha)).symm
  exact congr($hcomm ξ).symm

/-- If `y ∈ M.commutant` and `y * a = 0`, then `orbitSpan M a` lies in `y.ker`. -/
private theorem orbitSpan_le_ker {M : VonNeumannAlgebra H} {a y : H →L[ℂ] H}
    (hy : y ∈ M.commutant) (hya : y * a = 0) :
    orbitSpan M a ≤ y.ker := by
  rw [orbitSpan, Submodule.span_le]
  rintro _ ⟨x, hx, ξ, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker]
  have hyx : y * x = x * y := (mem_commutant_iff.1 hy x hx).symm
  calc y (x (a ξ))
    _ = (y * x) (a ξ) := rfl
    _ = (x * y) (a ξ) := by rw [hyx]
    _ = x ((y * a) ξ) := rfl
    _ = 0 := by rw [hya, zero_apply, map_zero]

/-- The orthogonal projection onto the closed span of the `M`-orbits `{x (a ξ) | x ∈ M, ξ ∈ H}`
belongs to `M.commutant`. -/
private theorem starProjection_closure_span_orbit_mem_commutant (M : VonNeumannAlgebra H)
    (a : H →L[ℂ] H) :
    (orbitSpan M a).topologicalClosure.starProjection ∈ M.commutant := by
  let A := M.toStarSubalgebra.toNonUnitalStarSubalgebra
  let O : H → Submodule ℂ H := fun ξ =>
    A.toNonUnitalSubalgebra.toSubmodule.map (ContinuousLinearMap.apply ℂ H (a ξ)).toLinearMap
  have hW_eq : orbitSpan M a = ⨆ ξ, O ξ := by
    have hset : {η : H | ∃ x ∈ M, ∃ ξ : H, x (a ξ) = η} = ⋃ ξ, (O ξ : Set H) := by
      ext η
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, SetLike.mem_coe, O, Submodule.mem_map,
        NonUnitalSubalgebra.mem_toSubmodule, ContinuousLinearMap.coe_coe,
        ContinuousLinearMap.apply_apply, A]
      exact ⟨fun ⟨x, hx, ξ, h⟩ => ⟨ξ, x, hx, h⟩, fun ⟨ξ, x, hx, h⟩ => ⟨x, hx, ξ, h⟩⟩
    rw [orbitSpan, hset, Submodule.span_iUnion]
    simp only [Submodule.span_eq]
  have hK_eq :
      (orbitSpan M a).topologicalClosure =
        (⨆ ξ, (O ξ).closure : ClosedSubmodule ℂ H).toSubmodule := by
    have gc : GaloisConnection (Submodule.closure : Submodule ℂ H → ClosedSubmodule ℂ H)
        ClosedSubmodule.toSubmodule := fun _ _ => Submodule.closure_le
    have hcl : (orbitSpan M a).closure = ⨆ ξ, (O ξ).closure := by
      rw [hW_eq]
      exact gc.l_iSup
    exact congrArg ClosedSubmodule.toSubmodule hcl
  rw [Submodule.starProjection_inj.2 hK_eq]
  refine starProjection_topologicalClosure_iSup_mem (fun ξ => (O ξ).closure) fun ξ => ?_
  rw [Submodule.starProjection_inj.2 (Submodule.toSubmodule_closure (O ξ)),
    ← SetLike.mem_coe, coe_commutant, ← coe_toStarSubalgebra]
  exact A.starProjection_topologicalClosure_map_apply_mem_centralizer (a ξ)

/-- **Geometric formula for the central support.** For `a ∈ M`, `M.centralSupport a` is the
orthogonal projection onto the closure of the linear span of `{x (a ξ) | x ∈ M, ξ ∈ H}`. -/
theorem centralSupport_eq_starProjection_closure_span {M : VonNeumannAlgebra H} {a : H →L[ℂ] H}
    (ha : a ∈ M) :
    M.centralSupport a =
      (Submodule.span ℂ {η : H | ∃ x ∈ M, ∃ ξ : H, x (a ξ) = η}).topologicalClosure.starProjection
      := by
  rw [← orbitSpan]
  set K : Submodule ℂ H := (orbitSpan M a).topologicalClosure
  -- Step 1: `orbitSpan M a` is invariant under `M.commutant` (so `K.starProjection ∈ M`) and is
  -- the span of the orbits `M (a ξ)` (so `K.starProjection ∈ M.commutant`).
  have hKM : K.starProjection ∈ M := by
    rw [IsStarProjection.mem_iff isStarProjection_starProjection M, Submodule.range_starProjection]
    exact fun y hy =>
      Submodule.topologicalClosure_mem_invtSubmodule (orbitSpan_mem_invtSubmodule_commutant ha hy)
  have hKC : K.starProjection ∈ M.commutant :=
    M.starProjection_closure_span_orbit_mem_commutant a
  -- Step 2: `K.starProjection * a = a` since `a ξ = 1 (a ξ) ∈ orbitSpan M a ≤ K`.
  have hKa : K.starProjection * a = a := by
    rw [ContinuousLinearMap.IsIdempotentElem.mul_eq_right_iff
        K.isIdempotentElem_starProjection a,
      Submodule.range_starProjection]
    rintro _ ⟨ξ, rfl⟩
    exact (orbitSpan M a).le_topologicalClosure (Submodule.subset_span ⟨1, one_mem M, ξ, rfl⟩)
  -- Step 3: Every central projection `z` with `z * a = a` satisfies `1 - z ∈ M.commutant` and
  -- `(1 - z) * a = 0`, so `orbitSpan M a ≤ (1 - z).ker ≤ z.range`, hence `K ≤ z.range`.
  refine le_antisymm
    ((centralSupport_le_iff isStarProjection_starProjection hKM hKC).2 hKa) ?_
  rw [← coe_centralSupportProjection]
  set z := M.centralSupportProjection a
  rw [← z.starProjection_range, Submodule.starProjection_le_starProjection_iff]
  refine (orbitSpan M a).topologicalClosure_minimal ?_
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range z.isStarProjection.isIdempotentElem)
  refine (orbitSpan_le_ker (sub_mem (one_mem M.commutant) (mem_inf.1 z.coe_mem).2) ?_).trans ?_
  · rw [sub_mul, one_mul, coe_centralSupportProjection, M.centralSupport_mul_self a, sub_self]
  · intro η hη
    exact ⟨η, (sub_eq_zero.1 (LinearMap.mem_ker.1 hη)).symm⟩

/-- **Central-support kernel theorem.** For `a ∈ M` and `y ∈ M.commutant`, `y * a = 0` holds if and
only if `y * M.centralSupport a = 0`. -/
theorem commutant_mul_eq_zero_iff_mul_centralSupport_eq_zero {M : VonNeumannAlgebra H}
    {a y : H →L[ℂ] H} (ha : a ∈ M) (hy : y ∈ M.commutant) :
    y * a = 0 ↔ y * M.centralSupport a = 0 := by
  refine ⟨fun hya => ?_, fun hyc => by
    rw [← M.centralSupport_mul_self a, ← mul_assoc, hyc, zero_mul]⟩
  rw [centralSupport_eq_starProjection_closure_span ha, ← orbitSpan]
  have hW_ker : (orbitSpan M a).topologicalClosure ≤ y.ker :=
    (orbitSpan M a).topologicalClosure_minimal (orbitSpan_le_ker hy hya) y.isClosed_ker
  ext ξ
  exact hW_ker (Submodule.starProjection_apply_mem _ ξ)

end VonNeumannAlgebra

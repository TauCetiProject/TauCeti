/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Order
public import Mathlib.Analysis.InnerProductSpace.Positive
public import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
public import TauCeti.Analysis.VonNeumannAlgebra.Lattice
import TauCeti.Analysis.CStarAlgebra.DedekindFinite

/-!
# Factors, cyclic and separating vectors, and tracial finiteness for von Neumann algebras

Let `M` be a concrete von Neumann algebra on a complex Hilbert space `H`.

* **Factors**: `M.IsFactor` holds when `(1 : H →L[ℂ] H) ≠ 0` and every central element
  `x ∈ M ∩ M'` is a complex scalar multiple of `1`, equivalently `Nontrivial H` and
  `M ⊓ M.commutant = ⊥` (`VonNeumannAlgebra.isFactor_iff_inf_commutant_eq_bot`). Taking the
  commutant preserves factorhood (`VonNeumannAlgebra.isFactor_commutant_iff`), and on a nontrivial
  Hilbert space both `⊤` and `⊥` are factors.
* **Cyclic and separating vectors**: `ξ : H` is cyclic for `M` (`M.IsCyclic ξ`) when the orbit
  `M ξ` is dense in `H`, and separating (`M.IsSeparating ξ`) when `x ξ = 0` forces `x = 0` for
  `x ∈ M`. Using the orthogonal projection onto the closed orbit `closure (M ξ)`, which belongs to
  `M'`, `ξ` is cyclic for `M` if and only if it is separating for `M'`
  (`VonNeumannAlgebra.isCyclic_iff_isSeparating_commutant`).
* **Normal functionals, tracial states, and finiteness**: `M.IsNormalFunctional τ` expresses strong
  continuity of `τ : M.toStarSubalgebra →ₗ[ℂ] ℂ` along increasing nets; every matrix-coefficient
  functional `x ↦ ⟪ξ, x η⟫_ℂ` (`M.innerLinearMap ξ η`) is normal. `M.IsTracialState τ` collects
  normalization, positivity, and traciality, while `M.IsFinite` states that every isometry in `M`
  is unitary (`star v * v = 1 → v * star v = 1`). Any von Neumann algebra carrying a
  projection-faithful additive trace is finite (`VonNeumannAlgebra.IsFinite.of_tracial`).

## References

* J. Peterson, *Notes on von Neumann Algebras* (2013), Proposition 2.1.3 and §3.2.
* C. Anantharaman and S. Popa, *An Introduction to II₁ Factors*, §§2.1, 2.5, and 6.1.
-/

public section

open Filter Topology
open scoped ComplexOrder InnerProductSpace

universe u

namespace VonNeumannAlgebra

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-! ### Factors -/

/-- A concrete von Neumann algebra `M` on `H` is a **factor** when `(1 : H →L[ℂ] H) ≠ 0` and every
element of the center `M ∩ M'` is a scalar multiple of the identity. -/
def IsFactor (M : VonNeumannAlgebra H) : Prop :=
  (1 : H →L[ℂ] H) ≠ 0 ∧
    ∀ x : H →L[ℂ] H, x ∈ M → x ∈ M.commutant → ∃ c : ℂ, x = c • (1 : H →L[ℂ] H)

theorem isFactor_def (M : VonNeumannAlgebra H) :
    M.IsFactor ↔
      (1 : H →L[ℂ] H) ≠ 0 ∧
        ∀ x : H →L[ℂ] H, x ∈ M → x ∈ M.commutant → ∃ c : ℂ, x = c • (1 : H →L[ℂ] H) :=
  Iff.rfl

/-- In a factor on `H`, the identity operator on `H` is nonzero. -/
theorem IsFactor.one_ne_zero {M : VonNeumannAlgebra H} (hM : M.IsFactor) :
    (1 : H →L[ℂ] H) ≠ 0 :=
  hM.1

/-- The underlying Hilbert space of a factor is nontrivial. -/
theorem IsFactor.nontrivial {M : VonNeumannAlgebra H} (hM : M.IsFactor) : Nontrivial H := by
  by_contra h
  rw [not_nontrivial_iff_subsingleton] at h
  exact hM.1 (Subsingleton.elim _ _)

/-- Every element in both a factor `M` and its commutant `M'` is a scalar multiple of `1`. -/
theorem IsFactor.eq_smul_one {M : VonNeumannAlgebra H} (hM : M.IsFactor) {x : H →L[ℂ] H}
    (hx : x ∈ M) (hx' : x ∈ M.commutant) : ∃ c : ℂ, x = c • (1 : H →L[ℂ] H) :=
  hM.2 x hx hx'

/-- No von Neumann algebra on a subsingleton Hilbert space is a factor. -/
theorem not_isFactor_of_subsingleton [Subsingleton H] (M : VonNeumannAlgebra H) :
    ¬ M.IsFactor :=
  fun hM => hM.1 (Subsingleton.elim _ _)

/-- `M` is a factor if and only if `H` is nontrivial and the center `M ⊓ M'` is the scalar algebra
`⊥`. -/
theorem isFactor_iff_inf_commutant_eq_bot (M : VonNeumannAlgebra H) :
    M.IsFactor ↔ Nontrivial H ∧ M ⊓ M.commutant = ⊥ := by
  refine ⟨fun hM => ⟨hM.nontrivial, le_antisymm (fun x hx => ?_) bot_le⟩, fun ⟨hH, hbot⟩ => ?_⟩
  · rw [mem_inf] at hx
    obtain ⟨c, rfl⟩ := hM.2 x hx.1 hx.2
    exact mem_bot.2 ⟨c, Algebra.algebraMap_eq_smul_one c⟩
  · refine ⟨one_ne_zero, fun x hx hx' => ?_⟩
    have hxbot : x ∈ (⊥ : VonNeumannAlgebra H) := hbot ▸ mem_inf.2 ⟨hx, hx'⟩
    obtain ⟨c, rfl⟩ := mem_bot.1 hxbot
    exact ⟨c, (Algebra.algebraMap_eq_smul_one c).symm⟩

/-- The commutant of a factor is a factor. -/
theorem IsFactor.commutant {M : VonNeumannAlgebra H} (hM : M.IsFactor) : M.commutant.IsFactor :=
  ⟨hM.1, fun x hx hx' => hM.2 x (by simpa using hx') hx⟩

@[simp]
theorem isFactor_commutant_iff (M : VonNeumannAlgebra H) : M.commutant.IsFactor ↔ M.IsFactor :=
  ⟨fun h => by simpa using h.commutant, IsFactor.commutant⟩

/-- On a nontrivial Hilbert space, `⊤ = B(H)` is a factor. -/
theorem isFactor_top [Nontrivial H] : (⊤ : VonNeumannAlgebra H).IsFactor := by
  rw [isFactor_iff_inf_commutant_eq_bot, commutant_top, top_inf_eq]
  exact ⟨inferInstance, rfl⟩

/-- On a nontrivial Hilbert space, the scalar algebra `⊥ = ℂ • 1` is a factor. -/
theorem isFactor_bot [Nontrivial H] : (⊥ : VonNeumannAlgebra H).IsFactor := by
  rw [← commutant_top, isFactor_commutant_iff]
  exact isFactor_top

/-! ### Cyclic and separating vectors -/

/-- A vector `ξ : H` is **cyclic** for `M` when the orbit `M ξ` is dense in `H`. -/
def IsCyclic (M : VonNeumannAlgebra H) (ξ : H) : Prop :=
  Dense (Set.range fun x : M => (x : H →L[ℂ] H) ξ)

theorem isCyclic_def (M : VonNeumannAlgebra H) (ξ : H) :
    M.IsCyclic ξ ↔ Dense (Set.range fun x : M => (x : H →L[ℂ] H) ξ) :=
  Iff.rfl

/-- A vector `ξ : H` is **separating** for `M` when `x ξ = 0` forces `x = 0` for `x ∈ M`. -/
def IsSeparating (M : VonNeumannAlgebra H) (ξ : H) : Prop :=
  ∀ x : M, (x : H →L[ℂ] H) ξ = 0 → x = 0

theorem isSeparating_def (M : VonNeumannAlgebra H) (ξ : H) :
    M.IsSeparating ξ ↔ ∀ x : M, (x : H →L[ℂ] H) ξ = 0 → x = 0 :=
  Iff.rfl

/-- Membership-predicate form of `VonNeumannAlgebra.IsSeparating`. -/
theorem isSeparating_iff (M : VonNeumannAlgebra H) (ξ : H) :
    M.IsSeparating ξ ↔ ∀ x ∈ M, x ξ = 0 → x = 0 :=
  ⟨fun h x hx hx0 => congr_arg Subtype.val (h ⟨x, hx⟩ hx0),
    fun h ⟨x, hx⟩ hx0 => Subtype.ext (h x hx hx0)⟩

/-- An operator in `M` that annihilates a separating vector is `0`. -/
theorem IsSeparating.eq_zero {M : VonNeumannAlgebra H} {ξ : H} (hξ : M.IsSeparating ξ)
    {x : H →L[ℂ] H} (hx : x ∈ M) (hx0 : x ξ = 0) : x = 0 :=
  (M.isSeparating_iff ξ).1 hξ x hx hx0

/-- Two operators in `M` agreeing on a separating vector are equal. -/
theorem IsSeparating.eq_of_apply_eq {M : VonNeumannAlgebra H} {ξ : H} (hξ : M.IsSeparating ξ)
    {x y : H →L[ℂ] H} (hx : x ∈ M) (hy : y ∈ M) (hxy : x ξ = y ξ) : x = y :=
  sub_eq_zero.1 <| hξ.eq_zero (sub_mem hx hy) (by simp [hxy])

/-- **Cyclic versus separating.** A vector is cyclic for `M` if and only if it is separating for
the commutant `M'`. -/
theorem isCyclic_iff_isSeparating_commutant (M : VonNeumannAlgebra H) (ξ : H) :
    M.IsCyclic ξ ↔ M.commutant.IsSeparating ξ := by
  refine ⟨fun hcyc => (M.commutant.isSeparating_iff ξ).2 fun y hy hy0 => ?_, fun hsep => ?_⟩
  · have hzero : Set.EqOn y (0 : H →L[ℂ] H) (Set.range fun x : M => (x : H →L[ℂ] H) ξ) := by
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      have hcomm : x * y = y * x := mem_commutant_iff.1 hy x hx
      calc y (x ξ) = (y * x) ξ := rfl
        _ = (x * y) ξ := by rw [hcomm]
        _ = x (y ξ) := rfl
        _ = 0 := by rw [hy0, map_zero]
    have hall : closure (Set.range fun x : M => (x : H →L[ℂ] H) ξ) ⊆ {v : H | y v = 0} :=
      closure_minimal hzero (isClosed_eq y.continuous continuous_zero)
    exact ContinuousLinearMap.ext fun v => hall (hcyc v)
  · set K : Submodule ℂ H :=
      (M.toStarSubalgebra.toSubalgebra.toSubmodule.map
        (ContinuousLinearMap.apply ℂ H ξ).toLinearMap).topologicalClosure with hK
    have hKcoe : (K : Set H) = closure (Set.range fun x : M => (x : H →L[ℂ] H) ξ) := by
      rw [hK, Submodule.topologicalClosure_coe, Submodule.map_coe]
      congr 1
      ext v
      exact ⟨fun ⟨x, hx, hxv⟩ => ⟨⟨x, hx⟩, hxv⟩, fun ⟨⟨x, hx⟩, hxv⟩ => ⟨x, hx, hxv⟩⟩
    have hp : K.starProjection ∈ M.commutant := by
      rw [VonNeumannAlgebra.IsStarProjection.mem_iff (isStarProjection_starProjection (U := K))
        M.commutant, M.commutant_commutant, K.range_starProjection]
      intro t ht
      rw [Module.End.mem_invtSubmodule]
      refine Submodule.topologicalClosure_minimal _ ?_
        ((Submodule.isClosed_topologicalClosure _).preimage t.continuous)
      rintro _ ⟨s, hs, rfl⟩
      exact Submodule.le_topologicalClosure _ ⟨t * s, M.mul_mem ht hs, rfl⟩
    have hξK : ξ ∈ K := Submodule.le_topologicalClosure _ ⟨1, M.one_mem, rfl⟩
    have h1p : (1 - K.starProjection) ξ = 0 := by
      rw [sub_apply, one_apply_eq_self, K.starProjection_eq_self_iff.2 hξK, sub_self]
    have hp1 : K.starProjection = 1 :=
      (sub_eq_zero.1 (hsep.eq_zero (sub_mem M.commutant.one_mem hp) h1p)).symm
    rw [IsCyclic, dense_iff_closure_eq, ← hKcoe]
    refine Set.eq_univ_of_forall fun v => ?_
    rw [SetLike.mem_coe, ← K.starProjection_eq_self_iff, hp1, one_apply_eq_self]

/-- A vector is separating for `M` if and only if it is cyclic for `M'`. -/
theorem isSeparating_iff_isCyclic_commutant (M : VonNeumannAlgebra H) (ξ : H) :
    M.IsSeparating ξ ↔ M.commutant.IsCyclic ξ := by
  rw [isCyclic_iff_isSeparating_commutant, commutant_commutant]

/-! ### Normal functionals, tracial states, and finiteness -/

/-- A linear functional on `M` is **normal** when it preserves limits along increasing nets in `M`
that converge in the strong operator topology. Index types in the universe of `H` suffice because
an increasing net may be replaced by its directed range in `M`. -/
def IsNormalFunctional (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₗ[ℂ] ℂ) : Prop :=
  ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (x : ι → M.toStarSubalgebra) (y : M.toStarSubalgebra),
    Monotone (fun i => (x i : H →L[ℂ] H)) →
    Tendsto (fun i => ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
      (x i : H →L[ℂ] H)) atTop
      (𝓝 (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H (y : H →L[ℂ] H))) →
    Tendsto (fun i => τ (x i)) atTop (𝓝 (τ y))

theorem isNormalFunctional_def (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₗ[ℂ] ℂ) :
    M.IsNormalFunctional τ ↔
      ∀ (ι : Type u) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
        (x : ι → M.toStarSubalgebra) (y : M.toStarSubalgebra),
        Monotone (fun i => (x i : H →L[ℂ] H)) →
        Tendsto (fun i => ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
          (x i : H →L[ℂ] H)) atTop
          (𝓝 (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H
            (y : H →L[ℂ] H))) →
        Tendsto (fun i => τ (x i)) atTop (𝓝 (τ y)) :=
  Iff.rfl

/-- The matrix-coefficient linear functional `x ↦ ⟪ξ, x η⟫_ℂ` on `M.toStarSubalgebra`. -/
noncomputable def innerLinearMap (M : VonNeumannAlgebra H) (ξ η : H) :
    M.toStarSubalgebra →ₗ[ℂ] ℂ where
  toFun x := ⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ
  map_add' x y := by simp [inner_add_right]
  map_smul' c x := by simp [inner_smul_right]

@[simp]
theorem innerLinearMap_apply (M : VonNeumannAlgebra H) (ξ η : H) (x : M.toStarSubalgebra) :
    M.innerLinearMap ξ η x = ⟪ξ, (x : H →L[ℂ] H) η⟫_ℂ :=
  (rfl)

/-- Every matrix-coefficient functional `x ↦ ⟪ξ, x η⟫_ℂ` on `M` is normal. -/
theorem isNormalFunctional_innerLinearMap (M : VonNeumannAlgebra H) (ξ η : H) :
    M.IsNormalFunctional (M.innerLinearMap ξ η) := by
  intro ι _ _ _ x y _ hxy
  rw [PointwiseConvergenceCLM.tendsto_iff_forall_tendsto] at hxy
  exact tendsto_const_nhds.inner (hxy η)

/-- A **tracial state** on `M`: a linear functional satisfying `τ 1 = 1`, `0 ≤ τ (star x * x)`,
and `τ (x * y) = τ (y * x)`. -/
def IsTracialState (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₗ[ℂ] ℂ) : Prop :=
  τ 1 = 1 ∧ (∀ x, 0 ≤ τ (star x * x)) ∧ ∀ x y, τ (x * y) = τ (y * x)

theorem isTracialState_def (M : VonNeumannAlgebra H) (τ : M.toStarSubalgebra →ₗ[ℂ] ℂ) :
    M.IsTracialState τ ↔ τ 1 = 1 ∧ (∀ x, 0 ≤ τ (star x * x)) ∧ ∀ x y, τ (x * y) = τ (y * x) :=
  Iff.rfl

/-- A von Neumann algebra `M` is **finite** when every isometry in `M` is unitary. -/
def IsFinite (M : VonNeumannAlgebra H) : Prop :=
  ∀ v ∈ M, star v * v = 1 → v * star v = 1

theorem isFinite_def (M : VonNeumannAlgebra H) :
    M.IsFinite ↔ ∀ v ∈ M, star v * v = 1 → v * star v = 1 :=
  Iff.rfl

/-- Any von Neumann algebra whose underlying star subalgebra is Dedekind-finite is finite. -/
theorem IsFinite.of_isDedekindFiniteMonoid (M : VonNeumannAlgebra H)
    [IsDedekindFiniteMonoid M.toStarSubalgebra] : M.IsFinite := by
  intro v hv hvv
  have hsub : (star ⟨v, hv⟩ : M.toStarSubalgebra) * ⟨v, hv⟩ = 1 := Subtype.ext hvv
  exact congr_arg Subtype.val (mul_eq_one_symm hsub)

/-- A von Neumann algebra carrying a projection-faithful additive trace on `M.toStarSubalgebra` is
finite. -/
theorem IsFinite.of_tracial (M : VonNeumannAlgebra H) {G : Type*} [AddZeroClass G]
    (τ : M.toStarSubalgebra →+ G) (htr : ∀ x y, τ (x * y) = τ (y * x))
    (hfaith : ∀ q : M.toStarSubalgebra, IsStarProjection q → τ q = 0 → q = 0) :
    M.IsFinite := by
  have := CStarAlgebra.isDedekindFiniteMonoid_of_tracial τ htr hfaith
  exact IsFinite.of_isDedekindFiniteMonoid M

end VonNeumannAlgebra

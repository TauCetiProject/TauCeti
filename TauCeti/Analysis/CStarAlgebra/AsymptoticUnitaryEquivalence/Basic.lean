/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Sequential
public import Mathlib.Analysis.CStarAlgebra.CStarMatrix
public import Mathlib.Analysis.CStarAlgebra.Unitary.Connected
public import Mathlib.Topology.Algebra.Star.Unitary
public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Order.ProjIcc

/-!
# Asymptotic unitary equivalence in a unital target

Two possibly nonunital star homomorphisms `φ, ψ : A →⋆ₙₐ[ℂ] B` into a unital C⋆-algebra `B` are
*asymptotically unitarily equivalent* (`TauCeti.AsymptoticallyUnitarilyEquivalent`) when there is a
norm-continuous path `u : C(ℝ≥0, unitary B)` such that `(u t : B) * φ a * star (u t : B) → ψ a` as
`t → ∞` for every `a : A`, with no condition on `u 0`. Requiring `u 0 = 1` defines a separate,
stronger relation (`TauCeti.StronglyAsymptoticallyUnitarilyEquivalent`): a fixed unitary conjugacy
`Ad u` is always asymptotically unitarily equivalent to `φ` via the constant path, whereas the
`u 0 = 1` relation requires an implementing path in the identity component of `unitary B`.

Concatenating a path from `1` to `u 0` on `[0, 1]` with `t ↦ u (t - 1)` on `[1, ∞)` shows that
`StronglyAsymptoticallyUnitarilyEquivalent φ ψ` holds if and only if some implementing path `u` for
`AsymptoticallyUnitarilyEquivalent φ ψ` satisfies `Joined 1 (u 0)`
(`TauCeti.stronglyAsymptoticallyUnitarilyEquivalent_iff_exists_joined_one`). In particular, the two
relations coincide whenever `unitary B` is path-connected.

Both relations are equivalence relations, imply `TauCeti.ApproximatelyUnitarilyEquivalent` (hence
preserve pointwise norms and injectivity), extend from dense subsets of `A` by equicontinuity, and
are preserved by precomposition (including restriction to closed star subalgebras via
`NonUnitalStarSubalgebraClass.subtype`), unital postcomposition, and finite matrix amplification
(`CStarMatrix.mapₙₐ`).

## References

* M. Rørdam, *Classification of Nuclear, Simple C⋆-Algebras*, Encyclopaedia of Mathematical
  Sciences 126, Springer, 2002, Definition 1.1.15 and §2.1.
* N. C. Phillips, *A classification theorem for nuclear purely infinite simple C⋆-algebras*,
  Doc. Math. 5 (2000), 49–114, Definition 1.1.3.
-/

public section

noncomputable section

open Filter Topology
open scoped CStarAlgebra NNReal unitInterval

namespace TauCeti

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]

/-- Asymptotic unitary equivalence of two possibly nonunital star homomorphisms into a unital
C⋆-algebra `B`, implemented by a continuous path `[0, ∞) → unitary B` with no condition at `0`. -/
def AsymptoticallyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  ∃ u : C(ℝ≥0, unitary B),
    ∀ a, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a))

/-- Unfolding characterization of `AsymptoticallyUnitarilyEquivalent`. -/
theorem asymptoticallyUnitarilyEquivalent_def (φ ψ : A →⋆ₙₐ[ℂ] B) :
    AsymptoticallyUnitarilyEquivalent φ ψ ↔
      ∃ u : C(ℝ≥0, unitary B),
        ∀ a, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a)) :=
  Iff.rfl

/-- Strong asymptotic unitary equivalence of two possibly nonunital star homomorphisms into a
unital C⋆-algebra `B`, implemented by a continuous path `[0, ∞) → unitary B` starting at `1`. -/
def StronglyAsymptoticallyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  ∃ u : C(ℝ≥0, unitary B), u 0 = 1 ∧
    ∀ a, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a))

/-- Unfolding characterization of `StronglyAsymptoticallyUnitarilyEquivalent`. -/
theorem stronglyAsymptoticallyUnitarilyEquivalent_def (φ ψ : A →⋆ₙₐ[ℂ] B) :
    StronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      ∃ u : C(ℝ≥0, unitary B), u 0 = 1 ∧
        ∀ a, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a)) :=
  Iff.rfl

section Helpers

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- Pointwise convergence of unitary conjugates on a dense subset extends to the whole source by
equicontinuity of contractions. -/
private theorem tendsto_conj_of_dense {ι : Type*} {l : Filter ι} (u : ι → unitary B)
    {s : Set A} (hs : Dense s)
    (hu : ∀ a ∈ s, Tendsto (fun i ↦ (u i : B) * φ a * star (u i : B)) l (𝓝 (ψ a))) (a : A) :
    Tendsto (fun i ↦ (u i : B) * φ a * star (u i : B)) l (𝓝 (ψ a)) := by
  let e (i : ι) := Unitary.conjStarAlgAut ℂ B (u i)
  have he : Equicontinuous (fun i x ↦ e i (φ x)) := by
    apply Metric.equicontinuous_of_continuity_modulus id tendsto_id
    intro x y i
    simpa only [id_eq, dist_eq_norm, ← map_sub, StarAlgEquiv.norm_map] using
      NonUnitalStarAlgHom.norm_apply_le φ (x - y)
  have hclosed : IsClosed {x : A | Tendsto (fun i ↦ e i (φ x)) l (𝓝 (ψ x))} :=
    he.isClosed_setOfPred_tendsto (map_continuous ψ)
  exact hclosed.closure_subset_iff.mpr (fun x hx ↦ hu x hx) (hs a)

/-- Reversing a unitary path swaps the source and target of asymptotic unitary conjugation. -/
private theorem tendsto_conj_star {u : C(ℝ≥0, unitary B)}
    (hu : ∀ a, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a))) (a : A) :
    Tendsto (fun t ↦ ((star (u t) : unitary B) : B) * ψ a *
      star ((star (u t) : unitary B) : B)) atTop (𝓝 (φ a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hnorm (t : ℝ≥0) :
      ‖((star (u t) : unitary B) : B) * ψ a * star ((star (u t) : unitary B) : B) - φ a‖ =
        ‖(u t : B) * φ a * star (u t : B) - ψ a‖ := by
    let e := Unitary.conjStarAlgAut ℂ B (u t)
    have hn := (StarAlgEquiv.isometry e.symm).dist_eq (ψ a) (e (φ a))
    rw [e.symm_apply_apply] at hn
    simpa only [e, dist_eq_norm, Unitary.conjStarAlgAut_symm_apply,
      Unitary.conjStarAlgAut_apply, Unitary.coe_star, star_star, norm_sub_rev] using hn
  simpa only [hnorm] using tendsto_iff_norm_sub_tendsto_zero.mp (hu a)

/-- Multiplying two unitary paths composes their asymptotic unitary conjugations. -/
private theorem tendsto_conj_mul {u v : C(ℝ≥0, unitary B)}
    (hu : ∀ a, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a)))
    (hv : ∀ a, Tendsto (fun t ↦ (v t : B) * ψ a * star (v t : B)) atTop (𝓝 (χ a))) (a : A) :
    Tendsto (fun t ↦ ((v t * u t : unitary B) : B) * φ a *
      star ((v t * u t : unitary B) : B)) atTop (𝓝 (χ a)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun _ ↦ norm_nonneg _) (fun t ↦ ?_)
    ((tendsto_iff_norm_sub_tendsto_zero.mp (hu a)).add
      (tendsto_iff_norm_sub_tendsto_zero.mp (hv a)) |>.trans (by simp))
  have heq : (v t : B) * ((u t : B) * φ a * star (u t : B) - ψ a) * star (v t : B) +
      ((v t : B) * ψ a * star (v t : B) - χ a) =
      ((v t * u t : unitary B) : B) * φ a * star ((v t * u t : unitary B) : B) - χ a := by
    simp [mul_sub, sub_mul, mul_assoc]
  rw [← heq]
  refine (norm_add_le _ _).trans_eq ?_
  simpa only [Unitary.coe_star] using congrArg
    (fun x : ℝ ↦ x + ‖(v t : B) * ψ a * star (v t : B) - χ a‖)
    ((CStarRing.norm_mul_coe_unitary _ (star (v t))).trans
      (CStarRing.norm_coe_unitary_mul (v t) _))

/-- Pushing a unitary path forward along a unital star homomorphism. -/
private def mapUnitaryPath [CStarAlgebra C] (ρ : B →⋆ₐ[ℂ] C) (u : C(ℝ≥0, unitary B)) :
    C(ℝ≥0, unitary C) where
  toFun t := Unitary.map (StarMonoidHom.ofClass ρ) (u t)
  continuous_toFun := Continuous.subtype_mk
    ((map_continuous ρ).comp (continuous_subtype_val.comp u.continuous)) _

private theorem tendsto_conj_mapUnitaryPath [CStarAlgebra C] (ρ : B →⋆ₐ[ℂ] C)
    {u : C(ℝ≥0, unitary B)}
    (hu : ∀ a, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a))) (a : A) :
    Tendsto (fun t ↦ ((mapUnitaryPath ρ u t : unitary C) : C) *
      (ρ.toNonUnitalStarAlgHom.comp φ) a * star ((mapUnitaryPath ρ u t : unitary C) : C))
      atTop (𝓝 ((ρ.toNonUnitalStarAlgHom.comp ψ) a)) := by
  have hEq (t : ℝ≥0) :
      ((mapUnitaryPath ρ u t : unitary C) : C) * ρ (φ a) *
          star ((mapUnitaryPath ρ u t : unitary C) : C) =
        ρ ((u t : B) * φ a * star (u t : B)) := by
    simp [mapUnitaryPath, StarMonoidHom.ofClass, map_star]
  simpa only [Function.comp_def, NonUnitalStarAlgHom.comp_apply,
    StarAlgHom.coe_toNonUnitalStarAlgHom, hEq] using
    ((map_continuous ρ).tendsto (ψ a)).comp (hu a)

/-- Scalar-diagonal unital star homomorphism `B →⋆ₐ[ℂ] CStarMatrix n n B`. -/
private def scalarMatrixStarAlgHom (n : Type*) [Fintype n] [DecidableEq n] :
    B →⋆ₐ[ℂ] CStarMatrix n n B :=
  CStarMatrix.ofMatrixStarAlgEquiv.toStarAlgHom.comp
    { Matrix.scalarAlgHom n ℂ with
      map_star' b := by
        ext i j
        by_cases hij : i = j <;> simp [Matrix.scalar_apply, hij, eq_comm] }

/-- Scalar-diagonal unitary conjugation acts entrywise on `CStarMatrix.mapₙₐ`. -/
private theorem tendsto_conj_scalarMatrix [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] [DecidableEq n] {u : C(ℝ≥0, unitary B)}
    (hu : ∀ a, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a)))
    (M : CStarMatrix n n A) :
    Tendsto (fun t ↦ ((mapUnitaryPath (scalarMatrixStarAlgHom n) u t : unitary _) :
        CStarMatrix n n B) * CStarMatrix.mapₙₐ φ M *
      star ((mapUnitaryPath (scalarMatrixStarAlgHom n) u t : unitary _) :
        CStarMatrix n n B))
      atTop (𝓝 (CStarMatrix.mapₙₐ ψ M)) := by
  have hentry (t : ℝ≥0) :
      ((mapUnitaryPath (scalarMatrixStarAlgHom n) u t : unitary _) : CStarMatrix n n B) *
          CStarMatrix.mapₙₐ φ M *
          star ((mapUnitaryPath (scalarMatrixStarAlgHom n) u t : unitary _) : CStarMatrix n n B) =
        CStarMatrix.ofMatrixL (Matrix.of fun i j ↦ (u t : B) * φ (M i j) * star (u t : B)) := by
    ext i j
    simp [mapUnitaryPath, scalarMatrixStarAlgHom, ← CStarMatrix.ofMatrix_eq_ofMatrixStarAlgEquiv,
      CStarMatrix.mul_apply, CStarMatrix.star_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      apply_ite star, StarMonoidHom.ofClass, ← CStarMatrix.ofMatrix_eq_ofMatrixL,
      CStarMatrix.ofMatrix_apply]
  have htarget :
      CStarMatrix.mapₙₐ ψ M = CStarMatrix.ofMatrixL (Matrix.of fun i j ↦ ψ (M i j)) := by
    ext i j
    simp [← CStarMatrix.ofMatrix_eq_ofMatrixL, CStarMatrix.ofMatrix_apply]
  simp only [hentry, htarget]
  exact CStarMatrix.ofMatrixL.continuous.continuousAt.tendsto.comp <|
    tendsto_pi_nhds.mpr fun i ↦ tendsto_pi_nhds.mpr fun j ↦ hu (M i j)

/-- Concatenating a path from `1` to `u 0` on `[0, 1]` with `t ↦ u (t - 1)` on `[1, ∞)`. -/
private def prependPathToOne (u : C(ℝ≥0, unitary B)) (γ : Path (1 : unitary B) (u 0)) :
    C(ℝ≥0, unitary B) where
  toFun t := if t ≤ 1 then γ (Set.projIcc 0 1 zero_le_one (t : ℝ)) else u (t - 1)
  continuous_toFun := by
    refine Continuous.if_le (γ.continuous.comp (continuous_projIcc.comp continuous_subtype_val))
      (u.continuous.comp (continuous_id.sub continuous_const)) continuous_id continuous_const ?_
    intro t ht
    subst ht
    simp

private theorem tendsto_sub_one_nnreal_atTop :
    Tendsto (fun t : ℝ≥0 ↦ t - 1) atTop atTop := by
  rw [tendsto_atTop_atTop]
  exact fun b ↦ ⟨b + 1, fun t ht ↦ le_tsub_of_add_le_right ht⟩

end Helpers

namespace AsymptoticallyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- A fixed unitary conjugacy gives asymptotic unitary equivalence via the constant path. -/
theorem of_unitary (u : unitary B) (h : ∀ a, (u : B) * φ a * star (u : B) = ψ a) :
    AsymptoticallyUnitarilyEquivalent φ ψ :=
  ⟨ContinuousMap.const ℝ≥0 u, fun a ↦ by simp [h a]⟩

/-- Asymptotic unitary equivalence is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : AsymptoticallyUnitarilyEquivalent φ φ :=
  of_unitary 1 (by simp)

/-- Asymptotic unitary equivalence is symmetric. -/
@[symm]
theorem symm (h : AsymptoticallyUnitarilyEquivalent φ ψ) :
    AsymptoticallyUnitarilyEquivalent ψ φ := by
  obtain ⟨u, hu⟩ := h
  exact ⟨⟨fun t ↦ star (u t), u.continuous.star⟩, tendsto_conj_star hu⟩

/-- Asymptotic unitary equivalence is transitive. -/
@[trans]
theorem trans (h₁ : AsymptoticallyUnitarilyEquivalent φ ψ)
    (h₂ : AsymptoticallyUnitarilyEquivalent ψ χ) :
    AsymptoticallyUnitarilyEquivalent φ χ := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  exact ⟨v * u, tendsto_conj_mul hu hv⟩

/-- Asymptotic unitary equivalence is an equivalence relation. -/
theorem equivalence : Equivalence (AsymptoticallyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Asymptotic unitary equivalence implies approximate unitary equivalence. -/
theorem approximatelyUnitarilyEquivalent (h : AsymptoticallyUnitarilyEquivalent φ ψ) :
    ApproximatelyUnitarilyEquivalent φ ψ := by
  obtain ⟨u, hu⟩ := h
  exact ApproximatelyUnitarilyEquivalent.of_tendsto u hu

/-- Asymptotically unitarily equivalent maps have the same pointwise norm. -/
theorem norm_eq (h : AsymptoticallyUnitarilyEquivalent φ ψ) (a : A) : ‖φ a‖ = ‖ψ a‖ :=
  h.approximatelyUnitarilyEquivalent.norm_eq a

/-- Asymptotic unitary equivalence preserves injectivity. -/
theorem injective_iff (h : AsymptoticallyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ :=
  h.approximatelyUnitarilyEquivalent.injective_iff

/-- Pointwise convergence along a continuous unitary path on a dense subset suffices for asymptotic
unitary equivalence. -/
theorem of_dense {s : Set A} (hs : Dense s) (u : C(ℝ≥0, unitary B))
    (hu : ∀ a ∈ s, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a))) :
    AsymptoticallyUnitarilyEquivalent φ ψ :=
  ⟨u, tendsto_conj_of_dense u hs hu⟩

/-- Precomposition preserves asymptotic unitary equivalence, without a unitality condition. -/
theorem precomp [NonUnitalCStarAlgebra C] (h : AsymptoticallyUnitarilyEquivalent φ ψ)
    (ρ : C →⋆ₙₐ[ℂ] A) : AsymptoticallyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, fun c ↦ hu (ρ c)⟩

/-- Unital postcomposition preserves asymptotic unitary equivalence. -/
theorem postcomp [CStarAlgebra C] (h : AsymptoticallyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₐ[ℂ] C) : AsymptoticallyUnitarilyEquivalent
      (ρ.toNonUnitalStarAlgHom.comp φ) (ρ.toNonUnitalStarAlgHom.comp ψ) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨mapUnitaryPath ρ u, tendsto_conj_mapUnitaryPath ρ hu⟩

/-- Finite matrix amplification preserves asymptotic unitary equivalence. -/
theorem mapMatrix [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] [DecidableEq n] (h : AsymptoticallyUnitarilyEquivalent φ ψ) :
    AsymptoticallyUnitarilyEquivalent
      (CStarMatrix.mapₙₐ φ : CStarMatrix n n A →⋆ₙₐ[ℂ] CStarMatrix n n B)
      (CStarMatrix.mapₙₐ ψ) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨mapUnitaryPath (scalarMatrixStarAlgHom n) u, tendsto_conj_scalarMatrix hu⟩

end AsymptoticallyUnitarilyEquivalent

/-- Strong asymptotic unitary equivalence holds if and only if some continuous unitary path
implementing asymptotic unitary equivalence starts in the identity path component of
`unitary B`. -/
theorem stronglyAsymptoticallyUnitarilyEquivalent_iff_exists_joined_one
    {φ ψ : A →⋆ₙₐ[ℂ] B} :
    StronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      ∃ u : C(ℝ≥0, unitary B), Joined (1 : unitary B) (u 0) ∧
        ∀ a, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a)) := by
  constructor
  · rintro ⟨u, hu0, hu⟩
    exact ⟨u, hu0 ▸ Joined.refl (1 : unitary B), hu⟩
  · rintro ⟨u, ⟨γ⟩, hu⟩
    refine ⟨prependPathToOne u γ, ?_, fun a ↦ ?_⟩
    · simp [prependPathToOne]
    · have hlim := (hu a).comp tendsto_sub_one_nnreal_atTop
      refine hlim.congr' ?_
      filter_upwards [eventually_gt_atTop (1 : ℝ≥0)] with t ht
      simp [prependPathToOne, not_le.mpr ht]

/-- When `unitary B` is path-connected, strong and unconstrained asymptotic unitary equivalence
coincide. -/
theorem stronglyAsymptoticallyUnitarilyEquivalent_iff_of_pathConnectedSpace
    [PathConnectedSpace (unitary B)] {φ ψ : A →⋆ₙₐ[ℂ] B} :
    StronglyAsymptoticallyUnitarilyEquivalent φ ψ ↔
      AsymptoticallyUnitarilyEquivalent φ ψ := by
  rw [stronglyAsymptoticallyUnitarilyEquivalent_iff_exists_joined_one,
    asymptoticallyUnitarilyEquivalent_def]
  exact exists_congr fun u ↦ and_iff_right (PathConnectedSpace.joined 1 (u 0))

namespace StronglyAsymptoticallyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- Strong asymptotic unitary equivalence implies asymptotic unitary equivalence. -/
theorem asymptoticallyUnitarilyEquivalent (h : StronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    AsymptoticallyUnitarilyEquivalent φ ψ := by
  obtain ⟨u, _, hu⟩ := h
  exact ⟨u, hu⟩

/-- Strong asymptotic unitary equivalence implies approximate unitary equivalence. -/
theorem approximatelyUnitarilyEquivalent (h : StronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    ApproximatelyUnitarilyEquivalent φ ψ :=
  h.asymptoticallyUnitarilyEquivalent.approximatelyUnitarilyEquivalent

/-- Conjugate maps by a unitary in the identity path component are strongly asymptotically
unitarily equivalent. -/
theorem of_joined_one (u : unitary B) (hu : Joined (1 : unitary B) u)
    (h : ∀ a, (u : B) * φ a * star (u : B) = ψ a) :
    StronglyAsymptoticallyUnitarilyEquivalent φ ψ :=
  stronglyAsymptoticallyUnitarilyEquivalent_iff_exists_joined_one.mpr
    ⟨ContinuousMap.const ℝ≥0 u, hu, fun a ↦ by simp [h a]⟩

/-- Conjugate maps by a unitary at distance strictly less than `2` from `1` are strongly
asymptotically unitarily equivalent. -/
theorem of_norm_sub_one_lt_two (u : unitary B) (hu : ‖(u : B) - 1‖ < 2)
    (h : ∀ a, (u : B) * φ a * star (u : B) = ψ a) :
    StronglyAsymptoticallyUnitarilyEquivalent φ ψ :=
  of_joined_one u (Unitary.joined 1 u hu) h

/-- Strong asymptotic unitary equivalence is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : StronglyAsymptoticallyUnitarilyEquivalent φ φ :=
  ⟨ContinuousMap.const ℝ≥0 1, rfl, fun a ↦ by simp⟩

/-- Strong asymptotic unitary equivalence is symmetric. -/
@[symm]
theorem symm (h : StronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    StronglyAsymptoticallyUnitarilyEquivalent ψ φ := by
  obtain ⟨u, hu0, hu⟩ := h
  exact ⟨⟨fun t ↦ star (u t), u.continuous.star⟩, by simp [hu0], tendsto_conj_star hu⟩

/-- Strong asymptotic unitary equivalence is transitive. -/
@[trans]
theorem trans (h₁ : StronglyAsymptoticallyUnitarilyEquivalent φ ψ)
    (h₂ : StronglyAsymptoticallyUnitarilyEquivalent ψ χ) :
    StronglyAsymptoticallyUnitarilyEquivalent φ χ := by
  obtain ⟨u, hu0, hu⟩ := h₁
  obtain ⟨v, hv0, hv⟩ := h₂
  exact ⟨v * u, by simp [hu0, hv0], tendsto_conj_mul hu hv⟩

/-- Strong asymptotic unitary equivalence is an equivalence relation. -/
theorem equivalence :
    Equivalence (StronglyAsymptoticallyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Strongly asymptotically unitarily equivalent maps have the same pointwise norm. -/
theorem norm_eq (h : StronglyAsymptoticallyUnitarilyEquivalent φ ψ) (a : A) :
    ‖φ a‖ = ‖ψ a‖ :=
  h.asymptoticallyUnitarilyEquivalent.norm_eq a

/-- Strong asymptotic unitary equivalence preserves injectivity. -/
theorem injective_iff (h : StronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ :=
  h.asymptoticallyUnitarilyEquivalent.injective_iff

/-- Pointwise convergence on a dense subset along a unitary path starting at `1` suffices for
strong asymptotic unitary equivalence. -/
theorem of_dense {s : Set A} (hs : Dense s) (u : C(ℝ≥0, unitary B)) (hu0 : u 0 = 1)
    (hu : ∀ a ∈ s, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a))) :
    StronglyAsymptoticallyUnitarilyEquivalent φ ψ :=
  ⟨u, hu0, tendsto_conj_of_dense u hs hu⟩

/-- Precomposition preserves strong asymptotic unitary equivalence, without a unitality
condition. -/
theorem precomp [NonUnitalCStarAlgebra C] (h : StronglyAsymptoticallyUnitarilyEquivalent φ ψ)
    (ρ : C →⋆ₙₐ[ℂ] A) : StronglyAsymptoticallyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) := by
  obtain ⟨u, hu0, hu⟩ := h
  exact ⟨u, hu0, fun c ↦ hu (ρ c)⟩

/-- Unital postcomposition preserves strong asymptotic unitary equivalence. -/
theorem postcomp [CStarAlgebra C] (h : StronglyAsymptoticallyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₐ[ℂ] C) : StronglyAsymptoticallyUnitarilyEquivalent
      (ρ.toNonUnitalStarAlgHom.comp φ) (ρ.toNonUnitalStarAlgHom.comp ψ) := by
  obtain ⟨u, hu0, hu⟩ := h
  refine ⟨mapUnitaryPath ρ u, ?_, tendsto_conj_mapUnitaryPath ρ hu⟩
  ext
  simp [mapUnitaryPath, hu0, StarMonoidHom.ofClass]

/-- Finite matrix amplification preserves strong asymptotic unitary equivalence. -/
theorem mapMatrix [PartialOrder A] [StarOrderedRing A] [PartialOrder B] [StarOrderedRing B]
    {n : Type*} [Fintype n] [DecidableEq n] (h : StronglyAsymptoticallyUnitarilyEquivalent φ ψ) :
    StronglyAsymptoticallyUnitarilyEquivalent
      (CStarMatrix.mapₙₐ φ : CStarMatrix n n A →⋆ₙₐ[ℂ] CStarMatrix n n B)
      (CStarMatrix.mapₙₐ ψ) := by
  obtain ⟨u, hu0, hu⟩ := h
  refine ⟨mapUnitaryPath (scalarMatrixStarAlgHom n) u, ?_, tendsto_conj_scalarMatrix hu⟩
  ext
  simp [mapUnitaryPath, hu0, StarMonoidHom.ofClass]

end StronglyAsymptoticallyUnitarilyEquivalent

end TauCeti

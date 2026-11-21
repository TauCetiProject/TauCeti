/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Sequential
public import TauCeti.Analysis.CStarAlgebra.Hom
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Asymptotic unitary equivalence in a unital target

Two possibly nonunital star homomorphisms `φ ψ : A → B` into a unital C⋆-algebra are
asymptotically unitarily equivalent when a norm-continuous path `u : [0, ∞) → U(B)` of target
unitaries satisfies `u t φ(a) u t* → ψ(a)` as `t → ∞`, for every `a`. Nothing is required of
`u 0`, so conjugation by any fixed unitary, in whatever path component of `U(B)`, is
asymptotically trivial (`of_unitary`). Requiring `u 0 = 1` would give a different, stronger
relation, which is not treated here.

This file proves that the relation is an equivalence relation, that it implies approximate
unitary equivalence (`ApproximatelyUnitarilyEquivalent`), and that it is compatible with
precomposition by any map (in particular restriction to a subalgebra) and with postcomposition
by a unital map. It is enough to check the convergence on a set whose generated star subalgebra
is dense (`of_dense_adjoin`).

This is the asymptotic counterpart of approximate unitary equivalence (Rørdam,
*Classification of nuclear, simple C*-algebras*, Encyclopaedia Math. Sci. 126, Definition
1.1.15), with the path indexed by `[0, ∞)` as in Phillips, *A classification theorem for
nuclear purely infinite simple C*-algebras*, Doc. Math. 5 (2000), and with unitaries of the
unital target rather than of the multiplier algebra.
-/

public section

open Filter Topology
open scoped NNReal CStarAlgebra

namespace TauCeti

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]

/-- Asymptotic unitary equivalence, implemented by a norm-continuous path of unitaries of the
unital target, indexed by `[0, ∞)`, with no condition at `0`. The source and the two maps need
not be unital. -/
def AsymptoticallyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  ∃ u : C(ℝ≥0, unitary B), ∀ a,
    Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a))

/-- Path characterization of asymptotic unitary equivalence with target unitaries. -/
theorem asymptoticallyUnitarilyEquivalent_def (φ ψ : A →⋆ₙₐ[ℂ] B) :
    AsymptoticallyUnitarilyEquivalent φ ψ ↔
      ∃ u : C(ℝ≥0, unitary B), ∀ a,
        Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a)) :=
  Iff.rfl

namespace AsymptoticallyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- A fixed unitary conjugacy gives asymptotic unitary equivalence, along a constant path. -/
theorem of_unitary (u : unitary B) (h : ∀ a, (u : B) * φ a * star (u : B) = ψ a) :
    AsymptoticallyUnitarilyEquivalent φ ψ :=
  ⟨ContinuousMap.const _ u, fun a ↦ by simp [h a]⟩

/-- Asymptotic unitary equivalence is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : AsymptoticallyUnitarilyEquivalent φ φ :=
  of_unitary 1 (by simp)

/-- Asymptotic unitary equivalence is symmetric, along the pointwise adjoint path. -/
@[symm]
theorem symm (h : AsymptoticallyUnitarilyEquivalent φ ψ) :
    AsymptoticallyUnitarilyEquivalent ψ φ := by
  obtain ⟨u, hu⟩ := h
  refine ⟨star u, fun a ↦ tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  -- Conjugation by `u t*` is an isometry, carrying the distance back to that of `hu`.
  have heq (t : ℝ≥0) : dist ((star u t : B) * ψ a * star (star u t : B)) (φ a) =
      dist (ψ a) ((u t : B) * φ a * star (u t : B)) := by
    let e := Unitary.conjStarAlgAut ℂ B (u t)
    have hn := (StarAlgEquiv.isometry e.symm).dist_eq (ψ a) (e (φ a))
    rw [e.symm_apply_apply] at hn
    simpa only [e, ContinuousMap.star_apply, Unitary.coe_star, star_star,
      Unitary.conjStarAlgAut_symm_apply, Unitary.conjStarAlgAut_apply] using hn
  simp_rw [heq, dist_comm (ψ a)]
  exact tendsto_iff_dist_tendsto_zero.mp (hu a)

/-- Asymptotic unitary equivalence is transitive, along the pointwise product path. -/
@[trans]
theorem trans (h₁ : AsymptoticallyUnitarilyEquivalent φ ψ)
    (h₂ : AsymptoticallyUnitarilyEquivalent ψ χ) : AsymptoticallyUnitarilyEquivalent φ χ := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  refine ⟨v * u, fun a ↦ tendsto_iff_dist_tendsto_zero.mpr ?_⟩
  -- Conjugating by `v t * u t` is conjugating by `u t`, then by the isometry `Ad (v t)`.
  have hle (t : ℝ≥0) : dist (((v * u) t : B) * φ a * star ((v * u) t : B)) (χ a) ≤
      dist ((u t : B) * φ a * star (u t : B)) (ψ a) +
        dist ((v t : B) * ψ a * star (v t : B)) (χ a) := by
    let e := Unitary.conjStarAlgAut ℂ B (v t)
    have hn := (StarAlgEquiv.isometry e).dist_eq ((u t : B) * φ a * star (u t : B)) (ψ a)
    have hvu : ((v * u) t : B) * φ a * star ((v * u) t : B) =
        e ((u t : B) * φ a * star (u t : B)) := by
      simp [e, mul_assoc]
    rw [hvu, ← hn]
    exact dist_triangle _ (e (ψ a)) _
  refine squeeze_zero (fun _ ↦ dist_nonneg) hle ?_
  simpa using (tendsto_iff_dist_tendsto_zero.mp (hu a)).add
    (tendsto_iff_dist_tendsto_zero.mp (hv a))

/-- The target-unitary asymptotic relation is an equivalence relation. -/
theorem equivalence : Equivalence (AsymptoticallyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Asymptotic unitary equivalence implies approximate unitary equivalence with target
unitaries. -/
theorem approximatelyUnitarilyEquivalent (h : AsymptoticallyUnitarilyEquivalent φ ψ) :
    ApproximatelyUnitarilyEquivalent φ ψ :=
  let ⟨u, hu⟩ := h
  ApproximatelyUnitarilyEquivalent.of_tendsto u hu

/-- A continuous path of target unitaries implements asymptotic unitary equivalence as soon as
it does so on a set whose generated star subalgebra is dense. -/
theorem of_dense_adjoin {s : Set A} (hs : Dense (NonUnitalStarAlgebra.adjoin ℂ s : Set A))
    (u : C(ℝ≥0, unitary B))
    (h : ∀ a ∈ s, Tendsto (fun t ↦ (u t : B) * φ a * star (u t : B)) atTop (𝓝 (ψ a))) :
    AsymptoticallyUnitarilyEquivalent φ ψ :=
  ⟨u, NonUnitalStarAlgHom.tendsto_of_dense_adjoin
    (f := fun t ↦ (Unitary.conjStarAlgAut ℂ B (u t)).toNonUnitalStarAlgHom.comp φ) hs
    (by simpa using h)⟩

/-- Precomposition preserves asymptotic unitary equivalence, without a unitality condition.
In particular the relation passes to restrictions to star subalgebras. -/
theorem precomp [NonUnitalCStarAlgebra C] (h : AsymptoticallyUnitarilyEquivalent φ ψ)
    (ρ : C →⋆ₙₐ[ℂ] A) : AsymptoticallyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) :=
  let ⟨u, hu⟩ := h
  ⟨u, fun a ↦ hu (ρ a)⟩

/-- Unital postcomposition preserves asymptotic unitary equivalence, along the image path. -/
theorem postcomp [CStarAlgebra C] (h : AsymptoticallyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₐ[ℂ] C) : AsymptoticallyUnitarilyEquivalent
      (ρ.toNonUnitalStarAlgHom.comp φ) (ρ.toNonUnitalStarAlgHom.comp ψ) := by
  obtain ⟨u, hu⟩ := h
  let m : C(unitary B, unitary C) :=
    ⟨Unitary.map (StarMonoidHom.ofClass ρ),
      ((map_continuous ρ).comp continuous_subtypeVal).subtype_mk _⟩
  refine ⟨m.comp u, fun a ↦ ?_⟩
  -- The image path is the composite with `ρ` on the underlying elements.
  have hm (x : unitary B) : (m x : C) = ρ x := rfl
  simpa only [ContinuousMap.comp_apply, hm, NonUnitalStarAlgHom.comp_apply,
    StarAlgHom.coe_toNonUnitalStarAlgHom, Function.comp_def, map_mul, map_star] using
    ((map_continuous ρ).tendsto (ψ a)).comp (hu a)

/-- Asymptotically unitarily equivalent maps have the same pointwise norm. -/
theorem norm_eq (h : AsymptoticallyUnitarilyEquivalent φ ψ) (a : A) : ‖φ a‖ = ‖ψ a‖ :=
  h.approximatelyUnitarilyEquivalent.norm_eq a

/-- Asymptotic unitary equivalence preserves injectivity. -/
theorem injective_iff (h : AsymptoticallyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ :=
  h.approximatelyUnitarilyEquivalent.injective_iff

end AsymptoticallyUnitarilyEquivalent

end TauCeti

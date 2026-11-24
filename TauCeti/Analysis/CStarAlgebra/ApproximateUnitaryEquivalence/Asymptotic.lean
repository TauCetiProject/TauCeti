/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Multiplier
public import TauCeti.Analysis.CStarAlgebra.Hom
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Asymptotic unitary equivalence

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

For a possibly nonunital target `B`, `MultiplierAsymptoticallyUnitarilyEquivalent` takes the
path in the unitary group of the multiplier algebra `𝓜(ℂ, B)`, continuous for the norm of
`𝓜(ℂ, B)`. It is the unital-target relation for the composites with `B → 𝓜(ℂ, B)`; it is an
equivalence relation, preserved by precomposition and by postcomposition with a nondegenerate
map, and it implies `MultiplierApproximatelyUnitarilyEquivalent`. For a unital target the two
versions coincide
(`multiplierAsymptoticallyUnitarilyEquivalent_iff_asymptoticallyUnitarilyEquivalent`).

This is the asymptotic counterpart of approximate unitary equivalence (Rørdam,
*Classification of nuclear, simple C*-algebras*, Encyclopaedia Math. Sci. 126, Definition
1.1.15), with the path indexed by `[0, ∞)` as in Phillips, *A classification theorem for
nuclear purely infinite simple C*-algebras*, Doc. Math. 5 (2000).
-/

public section

open Filter Topology
open scoped NNReal CStarAlgebra MultiplierAlgebra

namespace TauCeti

section Unital

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

/-- Unital postcomposition along a factorization `ρ ∘ ι = κ` carries asymptotic unitary
equivalence of the composites with `ι` to asymptotic unitary equivalence of the composites
with `κ`. -/
theorem postcomp_of_comp_eq [CStarAlgebra C] {D : Type*} [NonUnitalCStarAlgebra D]
    {φ ψ : A →⋆ₙₐ[ℂ] D} {ι : D →⋆ₙₐ[ℂ] B} {κ : D →⋆ₙₐ[ℂ] C}
    (h : AsymptoticallyUnitarilyEquivalent (ι.comp φ) (ι.comp ψ)) (ρ : B →⋆ₐ[ℂ] C)
    (hρ : ρ.toNonUnitalStarAlgHom.comp ι = κ) :
    AsymptoticallyUnitarilyEquivalent (κ.comp φ) (κ.comp ψ) := by
  subst hρ
  simpa only [NonUnitalStarAlgHom.comp_assoc] using h.postcomp ρ

/-- Asymptotically unitarily equivalent maps have the same pointwise norm. -/
theorem norm_eq (h : AsymptoticallyUnitarilyEquivalent φ ψ) (a : A) : ‖φ a‖ = ‖ψ a‖ :=
  h.approximatelyUnitarilyEquivalent.norm_eq a

/-- Asymptotic unitary equivalence preserves injectivity. -/
theorem injective_iff (h : AsymptoticallyUnitarilyEquivalent φ ψ) :
    Function.Injective φ ↔ Function.Injective ψ :=
  h.approximatelyUnitarilyEquivalent.injective_iff

end AsymptoticallyUnitarilyEquivalent

end Unital

section Multiplier

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [NonUnitalCStarAlgebra B]
  [NonUnitalCStarAlgebra C]

/-- Asymptotic unitary equivalence implemented by a norm-continuous path `u : [0, ∞) → U(𝓜(ℂ, B))`
of unitary multipliers: conjugation of `φ` by `u t` converges pointwise to `ψ` as `t → ∞`. It is
the target-unitary relation for the composites with the inclusion `B → 𝓜(ℂ, B)`. -/
def MultiplierAsymptoticallyUnitarilyEquivalent (φ ψ : A →⋆ₙₐ[ℂ] B) : Prop :=
  AsymptoticallyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
    ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ)

/-- The multiplier-unitary relation is the target-unitary relation inside `𝓜(ℂ, B)`. -/
theorem multiplierAsymptoticallyUnitarilyEquivalent_iff_coeHom (φ ψ : A →⋆ₙₐ[ℂ] B) :
    MultiplierAsymptoticallyUnitarilyEquivalent φ ψ ↔
      AsymptoticallyUnitarilyEquivalent ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp φ)
        ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ψ) :=
  Iff.rfl

/-- Path characterization of the multiplier-unitary relation, with the conjugates computed
in `B`. -/
theorem multiplierAsymptoticallyUnitarilyEquivalent_iff (φ ψ : A →⋆ₙₐ[ℂ] B) :
    MultiplierAsymptoticallyUnitarilyEquivalent φ ψ ↔
      ∃ u : C(ℝ≥0, unitary 𝓜(ℂ, B)), ∀ a,
        Tendsto (fun t ↦ DoubleCentralizer.conjStarAlgAut (u t) (φ a)) atTop (𝓝 (ψ a)) := by
  simp only [multiplierAsymptoticallyUnitarilyEquivalent_iff_coeHom,
    asymptoticallyUnitarilyEquivalent_def, NonUnitalStarAlgHom.comp_apply,
    DoubleCentralizer.coeHom_apply, ← DoubleCentralizer.coe_conjStarAlgAut_apply,
    DoubleCentralizer.tendsto_coe_iff]

namespace MultiplierAsymptoticallyUnitarilyEquivalent

variable {φ ψ χ : A →⋆ₙₐ[ℂ] B}

/-- Conjugacy by a fixed unitary multiplier gives the multiplier-unitary relation, through the
constant path. -/
theorem of_unitary (u : unitary 𝓜(ℂ, B))
    (h : ∀ a, DoubleCentralizer.conjStarAlgAut u (φ a) = ψ a) :
    MultiplierAsymptoticallyUnitarilyEquivalent φ ψ :=
  (multiplierAsymptoticallyUnitarilyEquivalent_iff φ ψ).2
    ⟨ContinuousMap.const _ u, fun a ↦ by simpa only [ContinuousMap.const_apply, h a] using
      tendsto_const_nhds⟩

/-- The multiplier-unitary relation is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : MultiplierAsymptoticallyUnitarilyEquivalent φ φ :=
  AsymptoticallyUnitarilyEquivalent.refl _

/-- The multiplier-unitary relation is symmetric. -/
@[symm]
theorem symm (h : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ) :
    MultiplierAsymptoticallyUnitarilyEquivalent ψ φ :=
  AsymptoticallyUnitarilyEquivalent.symm h

/-- The multiplier-unitary relation is transitive. -/
@[trans]
theorem trans (h₁ : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ)
    (h₂ : MultiplierAsymptoticallyUnitarilyEquivalent ψ χ) :
    MultiplierAsymptoticallyUnitarilyEquivalent φ χ :=
  AsymptoticallyUnitarilyEquivalent.trans h₁ h₂

/-- The multiplier-unitary relation is an equivalence relation. -/
theorem equivalence :
    Equivalence (MultiplierAsymptoticallyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Precomposition with any star homomorphism preserves the multiplier-unitary relation. -/
theorem precomp (h : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ) (ρ : C →⋆ₙₐ[ℂ] A) :
    MultiplierAsymptoticallyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) := by
  rw [multiplierAsymptoticallyUnitarilyEquivalent_iff_coeHom, ← NonUnitalStarAlgHom.comp_assoc,
    ← NonUnitalStarAlgHom.comp_assoc]
  exact AsymptoticallyUnitarilyEquivalent.precomp h ρ

/-- Postcomposition with a nondegenerate star homomorphism `ρ : B → C` preserves the
multiplier-unitary relation: the unital extension of `ρ` to the multiplier algebras carries
implementing paths to implementing paths. -/
theorem postcomp (h : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ) (ρ : B →⋆ₙₐ[ℂ] C)
    (hρ : ((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ).IsMultiplierNondegenerate) :
    MultiplierAsymptoticallyUnitarilyEquivalent (ρ.comp φ) (ρ.comp ψ) := by
  have hcomp : (((DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ).extendToMultiplier
      hρ).toNonUnitalStarAlgHom.comp (DoubleCentralizer.coeHom (𝕜 := ℂ)) =
      (DoubleCentralizer.coeHom (𝕜 := ℂ)).comp ρ := by
    refine NonUnitalStarAlgHom.ext fun b ↦ ?_
    simp
  simpa only [multiplierAsymptoticallyUnitarilyEquivalent_iff_coeHom,
    NonUnitalStarAlgHom.comp_assoc] using
    AsymptoticallyUnitarilyEquivalent.postcomp_of_comp_eq h _ hcomp

/-- The multiplier-unitary asymptotic relation implies the multiplier-unitary approximate
relation. -/
theorem multiplierApproximatelyUnitarilyEquivalent
    (h : MultiplierAsymptoticallyUnitarilyEquivalent φ ψ) :
    MultiplierApproximatelyUnitarilyEquivalent φ ψ :=
  (multiplierApproximatelyUnitarilyEquivalent_iff_coeHom φ ψ).2
    (AsymptoticallyUnitarilyEquivalent.approximatelyUnitarilyEquivalent h)

end MultiplierAsymptoticallyUnitarilyEquivalent

/-- For a unital target, implementing paths may be taken in `U(B)` or in `U(𝓜(ℂ, B))`: the
multiplier-unitary relation coincides with the target-unitary relation, since `B` is isomorphic
to its multiplier algebra. -/
theorem multiplierAsymptoticallyUnitarilyEquivalent_iff_asymptoticallyUnitarilyEquivalent
    {B : Type*} [CStarAlgebra B] {φ ψ : A →⋆ₙₐ[ℂ] B} :
    MultiplierAsymptoticallyUnitarilyEquivalent φ ψ ↔ AsymptoticallyUnitarilyEquivalent φ ψ := by
  rw [multiplierAsymptoticallyUnitarilyEquivalent_iff_coeHom]
  constructor
  · intro h
    simpa only [NonUnitalStarAlgHom.id_comp] using
      AsymptoticallyUnitarilyEquivalent.postcomp_of_comp_eq (κ := NonUnitalStarAlgHom.id ℂ B) h
        (DoubleCentralizer.coeStarAlgEquiv ℂ B).symm.toStarAlgHom (by simp)
  · intro h
    simpa only [StarAlgEquiv.toNonUnitalStarAlgHom_toStarAlgHom,
      DoubleCentralizer.coeStarAlgEquiv_toNonUnitalStarAlgHom] using
      AsymptoticallyUnitarilyEquivalent.postcomp h
        (DoubleCentralizer.coeStarAlgEquiv ℂ B).toStarAlgHom

end Multiplier

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.CStarAlgebra.ApproximateUnitaryEquivalence.Multiplier
public import Mathlib.Topology.Algebra.Star.Unitary

/-!
# Asymptotic unitary equivalence

Two star homomorphisms `φ ψ : A → B` into a unital C⋆-algebra are asymptotically unitarily
equivalent when some norm-continuous path `u : [0, ∞) → U(B)` of unitaries of `B` satisfies
`u t * φ a * (u t)⋆ → ψ a` as `t → ∞`, for every `a`. No condition is imposed on `u 0`: a map
and its conjugate by any fixed unitary are equivalent through a constant path, also when the
unitary is not connected to `1` in `U(B)`. Requiring `u 0 = 1` would give a different, stronger
relation.

For a possibly nonunital target `B`, `MultiplierAsymptoticallyUnitarilyEquivalent` takes the
path in the unitary group of the multiplier algebra `𝓜(ℂ, B)`, continuous for the norm of
`𝓜(ℂ, B)`. It is the unital-target relation for the composites with `B → 𝓜(ℂ, B)`, and for a
unital target the two coincide.

Asymptotic unitary equivalence implies approximate unitary equivalence with unitaries in the
same algebra. The asymptotic form of uniqueness for maps between AF algebras and Phillips's
uniqueness theorem for full maps into `O∞`-absorbing algebras are stated with it.

## Main results

* `AsymptoticallyUnitarilyEquivalent.equivalence` and
  `MultiplierAsymptoticallyUnitarilyEquivalent.equivalence`: both versions are equivalence
  relations.
* `AsymptoticallyUnitarilyEquivalent.of_unitary`: conjugacy by a fixed unitary gives asymptotic
  unitary equivalence.
* `AsymptoticallyUnitarilyEquivalent.precomp` and `AsymptoticallyUnitarilyEquivalent.postcomp`:
  the relation is preserved by precomposition with any map, in particular by restriction to a
  subalgebra, and by postcomposition with a unital one. For the multiplier version
  postcomposition is by a nondegenerate map, which extends to the multiplier algebras.
* `AsymptoticallyUnitarilyEquivalent.approximatelyUnitarilyEquivalent` and
  `MultiplierAsymptoticallyUnitarilyEquivalent.multiplierApproximatelyUnitarilyEquivalent`:
  asymptotic unitary equivalence implies approximate unitary equivalence.
* `multiplierAsymptoticallyUnitarilyEquivalent_iff_asymptoticallyUnitarilyEquivalent`: for a
  unital target, paths of unitaries may be taken in `B` or in `𝓜(ℂ, B)`.

## References

* M. Rørdam, *Classification of nuclear, simple C*-algebras*, in: Classification of Nuclear
  C*-Algebras. Entropy in Operator Algebras, Encyclopaedia Math. Sci. 126, Springer, 2002, §1.1.
* N. C. Phillips, *A classification theorem for nuclear purely infinite simple C*-algebras*,
  Doc. Math. 5 (2000), 49–114, §1.
-/

public section

open Filter Topology
open scoped CStarAlgebra MultiplierAlgebra NNReal

namespace TauCeti

section Unital

variable {A B C : Type*} [NonUnitalCStarAlgebra A] [CStarAlgebra B]

/-- Asymptotic unitary equivalence, implemented by a norm-continuous path `u : [0, ∞) → U(B)` of
unitaries of the unital target: `u t * φ a * (u t)⋆ → ψ a` as `t → ∞` for every `a`. The value
`u 0` is unconstrained, and the source and the two maps need not be unital. -/
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

/-- Conjugacy by a fixed unitary gives asymptotic unitary equivalence, through the constant
path. -/
theorem of_unitary (u : unitary B) (h : ∀ a, (u : B) * φ a * star (u : B) = ψ a) :
    AsymptoticallyUnitarilyEquivalent φ ψ :=
  ⟨ContinuousMap.const _ u, fun a ↦ by simpa only [ContinuousMap.const_apply, h a] using
    tendsto_const_nhds⟩

/-- Asymptotic unitary equivalence is reflexive. -/
@[refl, simp]
theorem refl (φ : A →⋆ₙₐ[ℂ] B) : AsymptoticallyUnitarilyEquivalent φ φ :=
  of_unitary 1 (by simp)

/-- Asymptotic unitary equivalence is symmetric, through the path of adjoint unitaries. -/
@[symm]
theorem symm (h : AsymptoticallyUnitarilyEquivalent φ ψ) :
    AsymptoticallyUnitarilyEquivalent ψ φ := by
  obtain ⟨u, hu⟩ := h
  refine ⟨star u, fun a ↦ tendsto_iff_norm_sub_tendsto_zero.2 ?_⟩
  have hn (t : ℝ≥0) : ‖((star u) t : B) * ψ a * star ((star u) t : B) - φ a‖ =
      ‖(u t : B) * φ a * star (u t : B) - ψ a‖ := by
    rw [← norm_neg, ← StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ B (u t))]
    simp [mul_sub, sub_mul, mul_assoc, ← mul_assoc (u t : B) (star (u t : B))]
  simpa only [hn] using tendsto_iff_norm_sub_tendsto_zero.1 (hu a)

/-- Asymptotic unitary equivalence is transitive, through the pointwise product of the
paths. -/
@[trans]
theorem trans (h₁ : AsymptoticallyUnitarilyEquivalent φ ψ)
    (h₂ : AsymptoticallyUnitarilyEquivalent ψ χ) : AsymptoticallyUnitarilyEquivalent φ χ := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  refine ⟨v * u, fun a ↦ ?_⟩
  have h₀ : Tendsto (fun t ↦ (v t : B) * ((u t : B) * φ a * star (u t : B) - ψ a) *
      star (v t : B)) atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun t ↦ ?_) (tendsto_iff_norm_sub_tendsto_zero.1 (hu a))
    simpa using (StarAlgEquiv.norm_map (Unitary.conjStarAlgAut ℂ B (v t))
      ((u t : B) * φ a * star (u t : B) - ψ a)).le
  simpa [mul_sub, sub_mul, mul_assoc] using h₀.add (hv a)

/-- Asymptotic unitary equivalence with target unitaries is an equivalence relation. -/
theorem equivalence : Equivalence (AsymptoticallyUnitarilyEquivalent (A := A) (B := B)) :=
  ⟨refl, fun h ↦ h.symm, fun h₁ h₂ ↦ h₁.trans h₂⟩

/-- Precomposition preserves asymptotic unitary equivalence, without a unitality condition. In
particular the relation passes to restrictions to subalgebras. -/
theorem precomp [NonUnitalCStarAlgebra C] (h : AsymptoticallyUnitarilyEquivalent φ ψ)
    (ρ : C →⋆ₙₐ[ℂ] A) : AsymptoticallyUnitarilyEquivalent (φ.comp ρ) (ψ.comp ρ) := by
  obtain ⟨u, hu⟩ := h
  exact ⟨u, fun a ↦ hu (ρ a)⟩

/-- Unital postcomposition preserves asymptotic unitary equivalence: the image of an
implementing path is an implementing path. -/
theorem postcomp [CStarAlgebra C] (h : AsymptoticallyUnitarilyEquivalent φ ψ)
    (ρ : B →⋆ₐ[ℂ] C) : AsymptoticallyUnitarilyEquivalent
      (ρ.toNonUnitalStarAlgHom.comp φ) (ρ.toNonUnitalStarAlgHom.comp ψ) := by
  obtain ⟨u, hu⟩ := h
  let w : C(unitary B, unitary C) :=
    ⟨Unitary.map (StarMonoidHom.ofClass ρ), continuous_induced_rng.2 <| by
      simpa only [Function.comp_def, Unitary.coe_map, StarMonoidHom.ofClass_coe] using
        (map_continuous ρ).comp continuous_subtypeVal⟩
  refine ⟨w.comp u, fun a ↦ (((map_continuous ρ).tendsto (ψ a)).comp (hu a)).congr fun t ↦ ?_⟩
  simp [w, map_star]

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

/-- Asymptotic unitary equivalence implies approximate unitary equivalence with target
unitaries. -/
theorem approximatelyUnitarilyEquivalent (h : AsymptoticallyUnitarilyEquivalent φ ψ) :
    ApproximatelyUnitarilyEquivalent φ ψ := by
  obtain ⟨u, hu⟩ := h
  exact ApproximatelyUnitarilyEquivalent.of_tendsto u hu

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

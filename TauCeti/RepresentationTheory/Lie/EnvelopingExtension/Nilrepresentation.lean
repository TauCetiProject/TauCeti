/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Lie.EnvelopingExtension.Nilpotent
public import TauCeti.RepresentationTheory.Lie.CofiniteKernel
public import TauCeti.Algebra.Lie.UniversalEnveloping.CofiniteRefinement

/-!
# Extending nilrepresentations across split ideal extensions

Let `ψ : H →ₗ⁅K⁆ LieDerivation K S S` define a split extension `S ⋊⁅ψ⁆ H` of Lie algebras over a
field, with `S` finite-dimensional, and let `σ` be a finite-dimensional representation of `S`. This
file extends `σ` to a finite-dimensional representation `ρ` of `S ⋊⁅ψ⁆ H` that keeps control of
the kernel and of nilpotence on `S`:

* every element of `S` killed by `ρ` is killed by `σ`;
* an element of `S` acts nilpotently under `ρ` exactly when it does under `σ`.

The construction works whenever every derivation `ψ h` takes values in a Lie ideal `N` of `S` that
acts nilpotently under `σ`. The kernel `I` of the enveloping-algebra extension of `σ` is a cofinite
two-sided ideal of `U(S)`, and a power of `I ⊔ N.envelopingIdeal` refines it to a cofinite ideal `J`
stable under the lifted derivations. The representation is then the multiplication-plus-derivation
action of `S ⋊⁅ψ⁆ H` on `U(S) ⧸ J`.

Two choices of `N` give the two cases of Fulton–Harris, Proposition E.5:

* in characteristic zero, every derivation of a solvable `S` takes values in its nilradical, so a
  nilrepresentation of `S` extends; the extension is again a nilrepresentation when the nilradical
  of `S ⋊⁅ψ⁆ H` lies in that of `S`;
* in any characteristic, when `S ⋊⁅ψ⁆ H` is nilpotent, a representation of `S` by nilpotent
  operators extends to one of `S ⋊⁅ψ⁆ H` by nilpotent operators.

Iterating these extensions along a flag of ideals is how a faithful nilrepresentation of the centre
grows into a representation of the whole Lie algebra in the proof of Ado's theorem.

## Main results

* `TauCeti.exists_semiDirectSum_rep_of_forall_mem`: the extension for derivations with values in a
  Lie ideal acting nilpotently.
* `TauCeti.exists_semiDirectSum_rep_of_isSolvable`: in characteristic zero, a nilrepresentation of a
  solvable ideal extends, and the extension is a nilrepresentation when the nilradical of the
  extension lies in that of the ideal.
* `TauCeti.exists_semiDirectSum_rep_of_isNilpotent`: on a nilpotent split extension, a
  representation by nilpotent operators extends to one by nilpotent operators.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2,
  Proposition E.5.
* S. Asgarli, [*Ado's Theorem*](https://personal.math.ubc.ca/~reichst/Ado%27s-Theorem.pdf),
  Proposition 2.
-/

public section

namespace TauCeti

open _root_.LieAlgebra

universe u v w x

attribute [local instance 100] LieRing.ofAssociativeRing

variable {K : Type u} {S : Type v} {H : Type w} {V : Type x}
  [Field K] [LieRing S] [LieAlgebra K S] [FiniteDimensional K S]
  [LieRing H] [LieAlgebra K H]
  [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  (ψ : H →ₗ⁅K⁆ LieDerivation K S S)

/-- The enveloping ideal behind the extensions in this file: a cofinite two-sided ideal of `U(S)`,
stable under the lifted derivations `ψ h`, contained in the kernel of the enveloping extension of
`σ`, and with the same nilpotent generators as `σ`. -/
private theorem exists_stable_envelopingIdeal (N : LieIdeal K S) (σ : S →ₗ⁅K⁆ Module.End K V)
    (hσ : ∀ s ∈ N, IsNilpotent (σ s)) (hψ : ∀ h s, ψ h s ∈ N) :
    ∃ (J : Ideal (UniversalEnvelopingAlgebra K S)) (_ : J.IsTwoSided)
      (_ : ∀ h : H, UniversalEnvelopingAlgebra.envelopingDerivation K S (ψ h) ∈
        stableDerivations K (J.restrictScalars K)),
      FiniteDimensional K (UniversalEnvelopingAlgebra K S ⧸ J) ∧
      J ≤ RingHom.ker (UniversalEnvelopingAlgebra.lift K σ) ∧
      ∀ s, IsNilpotent (Ideal.Quotient.mk J (UniversalEnvelopingAlgebra.ι K s)) ↔
        IsNilpotent (σ s) := by
  let f := (UniversalEnvelopingAlgebra.lift K σ).toRingHom
  let I := RingHom.ker f
  have : FiniteDimensional K (UniversalEnvelopingAlgebra K S ⧸ I) :=
    UniversalEnvelopingAlgebra.finiteDimensional_quotient_ker_lift K S σ
  have hI (s : S) : IsNilpotent (Ideal.Quotient.mk I (UniversalEnvelopingAlgebra.ι K s)) ↔
      IsNilpotent (σ s) := by
    rw [← IsNilpotent.map_iff (RingHom.kerLift_injective f), RingHom.kerLift_mk]
    simp only [f, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, UniversalEnvelopingAlgebra.lift_ι_apply]
  obtain ⟨n, hle, hfin, hstable, hnil⟩ :=
    N.exists_cofinite_refinement_stableDerivations I fun s hs ↦ (hI s).mpr (hσ s hs)
  exact ⟨_, inferInstance, fun h ↦ hstable (ψ h) (hψ h), hfin, hle, fun s ↦ by rw [hnil, hI]⟩

/-- A finite-dimensional representation `σ` of `S` extends to a finite-dimensional representation
`ρ` of the split extension `S ⋊⁅ψ⁆ H`, provided every derivation `ψ h` takes values in a Lie ideal
`N` of `S` whose elements act nilpotently under `σ`. The extension detects every direction of `S`
that `σ` detects, an element of `S` acts nilpotently under `ρ` exactly when it does under `σ`, and
when all of `S` acts nilpotently under `σ`, every element whose derivation is locally nilpotent acts
nilpotently under `ρ`. -/
theorem exists_semiDirectSum_rep_of_forall_mem (N : LieIdeal K S) (σ : S →ₗ⁅K⁆ Module.End K V)
    (hσ : ∀ s ∈ N, IsNilpotent (σ s)) (hψ : ∀ h s, ψ h s ∈ N) :
    ∃ (W : Type (max u v)) (_ : AddCommGroup W) (_ : Module K W) (_ : FiniteDimensional K W)
      (ρ : S ⋊⁅ψ⁆ H →ₗ⁅K⁆ Module.End K W),
      (ρ.comp (SemiDirectSum.inl ψ)).ker ≤ σ.ker ∧
      (∀ s, IsNilpotent (ρ (SemiDirectSum.inl ψ s)) ↔ IsNilpotent (σ s)) ∧
      ((∀ s, IsNilpotent (σ s)) → ∀ y : S ⋊⁅ψ⁆ H,
        (∀ s, ∃ n : ℕ, ((ψ y.right).toLinearMap ^ n) s = 0) → IsNilpotent (ρ y)) := by
  obtain ⟨J, _, hJ, hfin, hle, hJnil⟩ := exists_stable_envelopingIdeal ψ N σ hσ hψ
  refine ⟨_, inferInstance, inferInstance, hfin, envelopingQuotientRep K S ψ J hJ,
    ker_envelopingQuotientRep_comp_inl_le K S ψ J hJ σ hle, fun s ↦ ?_, fun hall y hy ↦
      isNilpotent_envelopingQuotientRep_of_locallyNilpotent K S ψ J hJ
        (fun s ↦ (hJnil s).mpr (hall s)) y hy⟩
  rw [SemiDirectSum.inl_eq_mk, envelopingQuotientRep_mk_zero, LinearMap.isNilpotent_mulLeft_iff,
    hJnil]

/-- **Extension of nilrepresentations across a split solvable ideal.** In characteristic zero, a
finite-dimensional representation of a solvable `S` on which the nilradical acts nilpotently extends
to a finite-dimensional representation `ρ` of `S ⋊⁅ψ⁆ H` that detects every direction of `S`
detected by `σ`. When the nilradical of `S ⋊⁅ψ⁆ H` lies in the image of the nilradical of `S`, the
extension is again a nilrepresentation. -/
theorem exists_semiDirectSum_rep_of_isSolvable [CharZero K] [IsSolvable S]
    (σ : S →ₗ⁅K⁆ Module.End K V) (hσ : ∀ s ∈ LieAlgebra.nilradical K S, IsNilpotent (σ s))
    (hnr : (LieAlgebra.nilradical K (S ⋊⁅ψ⁆ H)).toSubmodule ≤
      (LieAlgebra.nilradical K S).toSubmodule.map (SemiDirectSum.inl ψ).toLinearMap) :
    ∃ (W : Type (max u v)) (_ : AddCommGroup W) (_ : Module K W) (_ : FiniteDimensional K W)
      (ρ : S ⋊⁅ψ⁆ H →ₗ⁅K⁆ Module.End K W),
      (ρ.comp (SemiDirectSum.inl ψ)).ker ≤ σ.ker ∧
      ∀ y ∈ LieAlgebra.nilradical K (S ⋊⁅ψ⁆ H), IsNilpotent (ρ y) := by
  obtain ⟨W, _, _, _, ρ, hker, hρ, -⟩ := exists_semiDirectSum_rep_of_forall_mem ψ
    (LieAlgebra.nilradical K S) σ hσ fun h s ↦ (ψ h).apply_mem_nilradical_of_isSolvable s
  refine ⟨W, _, _, inferInstance, ρ, hker, fun y hy ↦ ?_⟩
  obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp (hnr hy)
  exact (hρ s).mpr (hσ s hs)

/-- **Extension of nilpotent representations across a nilpotent split extension.** Over any field,
if `S ⋊⁅ψ⁆ H` is nilpotent, a finite-dimensional representation of `S` by nilpotent operators
extends to a finite-dimensional representation of `S ⋊⁅ψ⁆ H` by nilpotent operators that detects
every direction of `S` detected by `σ`. -/
theorem exists_semiDirectSum_rep_of_isNilpotent [LieRing.IsNilpotent (S ⋊⁅ψ⁆ H)]
    (σ : S →ₗ⁅K⁆ Module.End K V) (hσ : ∀ s, IsNilpotent (σ s)) :
    ∃ (W : Type (max u v)) (_ : AddCommGroup W) (_ : Module K W) (_ : FiniteDimensional K W)
      (ρ : S ⋊⁅ψ⁆ H →ₗ⁅K⁆ Module.End K W),
      (ρ.comp (SemiDirectSum.inl ψ)).ker ≤ σ.ker ∧ ∀ y, IsNilpotent (ρ y) := by
  obtain ⟨J, _, hJ, hfin, hle, hJnil⟩ :=
    exists_stable_envelopingIdeal ψ ⊤ σ (fun s _ ↦ hσ s) fun _ _ ↦ LieSubmodule.mem_top _
  exact ⟨_, inferInstance, inferInstance, hfin, envelopingQuotientRep K S ψ J hJ,
    ker_envelopingQuotientRep_comp_inl_le K S ψ J hJ σ hle,
    isNilpotent_envelopingQuotientRep_of_isNilpotent K S ψ J hJ fun s _ ↦ (hJnil s).mpr (hσ s)⟩

end TauCeti

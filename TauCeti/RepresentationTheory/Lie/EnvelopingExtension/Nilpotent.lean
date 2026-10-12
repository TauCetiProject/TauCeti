/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Lie.EnvelopingExtension.Basic
public import TauCeti.Algebra.Lie.NilpotentExtension
public import TauCeti.Algebra.Lie.SemiDirect.AdNilpotent

/-!
# Nilpotence of representations on enveloping quotients

On a stable enveloping quotient that is Noetherian over the coefficient ring, the
multiplication-plus-derivation action is nilpotent on an element `(s, h)` when every ideal
element acts nilpotently by multiplication and the complementary quotient operator is
nilpotent. Local nilpotence of `ψ(h)` suffices for the latter condition. The two summands
need not commute: the ideal summand is normalized by the complementary summand, so the
nilpotent-extension lemma applies.

For a nilpotent split Lie extension, nilpotence of its adjoint action supplies the condition
on `ψ(h)`. Consequently every element of the extension acts nilpotently on any Noetherian
stable quotient where the images of the ideal's nilradical are nilpotent.
When the ambient nilradical is contained in the embedded nilradical of the ideal, nilpotence
control instead follows from the multiplication action alone, without a finiteness hypothesis
on the quotient. When the quotient is finite dimensional over a field, these results give
nilrepresentations of the extension.

The argument combines `LieSubalgebra.isNilpotent_toEnd_of_mem_lieSpan_insert_of_forall` with
the descended-derivation nilpotence theorem used by
`TauCeti.isNilpotent_envelopingQuotientRep_inr`.

## References

* W. Fulton and J. Harris, *Representation Theory: A First Course*, Appendix E, §E.2,
  Proposition E.5, for nilpotence control in the split-extension construction.
-/

public section

namespace TauCeti

open _root_.LieAlgebra
open TauCeti.UniversalEnvelopingAlgebra

universe u v w

variable (R : Type u) (S : Type v) {H : Type w}
  [CommRing R] [LieRing S] [LieAlgebra R S] [LieRing H] [LieAlgebra R H]

attribute [local instance 100] LieRing.ofAssociativeRing

local notation "U" => _root_.UniversalEnvelopingAlgebra R S

variable (ψ : H →ₗ⁅R⁆ LieDerivation R S S)
  (J : Ideal (_root_.UniversalEnvelopingAlgebra R S)) [J.IsTwoSided]
  (hJ : ∀ h : H, envelopingDerivation R S (ψ h) ∈
    stableDerivations R (J.restrictScalars R))

/-- If all ideal generators have nilpotent images and the complementary quotient operator is
nilpotent, the full multiplication-plus-derivation operator is nilpotent. The quotient need
only be Noetherian over the coefficient ring; the two operators need not commute. -/
theorem isNilpotent_envelopingQuotientRep [IsNoetherian R (U ⧸ J)]
    (hnil : ∀ s : S, IsNilpotent
      (Ideal.Quotient.mk J (_root_.UniversalEnvelopingAlgebra.ι R s)))
    (x : S ⋊⁅ψ⁆ H)
    (hH : IsNilpotent
      (envelopingQuotientRep R S ψ J hJ (SemiDirectSum.inr ψ x.right))) :
    IsNilpotent (envelopingQuotientRep R S ψ J hJ x) := by
  let ρ := envelopingQuotientRep R S ψ J hJ
  let K := (ρ.comp (SemiDirectSum.inl ψ)).range
  have hK : ∀ z ∈ K, IsNilpotent (LieModule.toEnd R (Module.End R (U ⧸ J)) (U ⧸ J) z) := by
    intro z hz
    obtain ⟨s, rfl⟩ := (LieHom.mem_range _ _).mp hz
    simpa only [LieModule.toEnd_module_end, LieHom.id_apply, LieHom.comp_apply,
      ρ, SemiDirectSum.inl_eq_mk, envelopingQuotientRep_mk_zero,
      LinearMap.isNilpotent_mulLeft_iff] using hnil s
  have hy : ρ (SemiDirectSum.inr ψ x.right) ∈ K.normalizer := by
    rw [LieSubalgebra.mem_normalizer_iff]
    intro z hz
    obtain ⟨s, rfl⟩ := (LieHom.mem_range _ _).mp hz
    rw [LieHom.comp_apply, ← ρ.map_lie]
    have hbr : ⁅SemiDirectSum.inr ψ x.right, SemiDirectSum.inl ψ s⁆ =
        SemiDirectSum.inl ψ (ψ x.right s) := by
      simp only [SemiDirectSum.inr_eq_mk, SemiDirectSum.inl_eq_mk,
        SemiDirectSum.lie_eq_mk, zero_lie, map_zero, sub_zero, zero_add, lie_zero]
    rw [hbr]
    exact (ρ.comp (SemiDirectSum.inl ψ)).mem_range_self _
  have hnilH : IsNilpotent (LieModule.toEnd R (Module.End R (U ⧸ J)) (U ⧸ J)
      (ρ (SemiDirectSum.inr ψ x.right))) := by
    simp only [LieModule.toEnd_module_end, LieHom.id_apply]
    exact hH
  have hsum := K.isNilpotent_toEnd_of_mem_lieSpan_insert_of_forall hy hK hnilH
    (K.smul_add_mem_lieSpan_insert hy (1 : R)
      ((ρ.comp (SemiDirectSum.inl ψ)).mem_range_self x.left))
  simpa only [LieModule.toEnd_module_end, LieHom.id_apply, one_smul,
    LieHom.comp_apply, ← map_add, SemiDirectSum.inr_eq_mk, SemiDirectSum.inl_eq_mk,
    SemiDirectSum.add_eq_mk, zero_add, add_zero] using hsum

/-- Local nilpotence of the complementary derivation and nilpotence of all ideal-generator
images imply nilpotence of the full action on a Noetherian stable enveloping quotient. -/
theorem isNilpotent_envelopingQuotientRep_of_locallyNilpotent [IsNoetherian R (U ⧸ J)]
    (hnil : ∀ s : S, IsNilpotent
      (Ideal.Quotient.mk J (_root_.UniversalEnvelopingAlgebra.ι R s)))
    (x : S ⋊⁅ψ⁆ H)
    (hψ : ∀ s : S, ∃ n : ℕ, ((ψ x.right).toLinearMap ^ n) s = 0) :
    IsNilpotent (envelopingQuotientRep R S ψ J hJ x) :=
  isNilpotent_envelopingQuotientRep R S ψ J hJ hnil x
    (isNilpotent_envelopingQuotientRep_inr R S ψ J hJ x.right hψ)

/-- On a nilpotent split extension, every element acts nilpotently on the stable enveloping
quotient whenever the images of the ideal's nilradical are nilpotent. -/
theorem isNilpotent_envelopingQuotientRep_of_isNilpotent [IsNoetherian R (U ⧸ J)]
    [LieRing.IsNilpotent (S ⋊⁅ψ⁆ H)]
    (hnil : ∀ s : S, s ∈ LieAlgebra.nilradical R S → IsNilpotent
      (Ideal.Quotient.mk J (_root_.UniversalEnvelopingAlgebra.ι R s)))
    (x : S ⋊⁅ψ⁆ H) : IsNilpotent (envelopingQuotientRep R S ψ J hJ x) := by
  have : LieRing.IsNilpotent S :=
    (SemiDirectSum.inl_injective ψ).lieAlgebra_isNilpotent
  apply isNilpotent_envelopingQuotientRep_of_locallyNilpotent R S ψ J hJ
    (fun s ↦ hnil s (by simp)) x
  have hψ := SemiDirectSum.isNilpotent_derivation_of_isNilpotent_ad_inr ψ x.right
    (LieModule.isNilpotent_toEnd_of_isNilpotent R (S ⋊⁅ψ⁆ H) (S ⋊⁅ψ⁆ H)
      (SemiDirectSum.inr ψ x.right))
  obtain ⟨n, hn⟩ := hψ
  exact fun s ↦ ⟨n, by simp [hn]⟩

/-- If the ambient nilradical lies in the embedded nilradical of the ideal and the images of
the ideal's nilradical are nilpotent, every element of the ambient nilradical acts nilpotently.
This includes equality of the two nilradicals and requires no finiteness of the quotient. -/
theorem isNilpotent_envelopingQuotientRep_of_mem_nilradical
    (hnil : ∀ s : S, s ∈ LieAlgebra.nilradical R S → IsNilpotent
      (Ideal.Quotient.mk J (_root_.UniversalEnvelopingAlgebra.ι R s)))
    (hnr : LieSubmodule.toSubmodule (LieAlgebra.nilradical R (S ⋊⁅ψ⁆ H)) ≤
      (LieSubmodule.toSubmodule (LieAlgebra.nilradical R S)).map
        (SemiDirectSum.inl ψ).toLinearMap)
    {x : S ⋊⁅ψ⁆ H} (hx : x ∈ LieAlgebra.nilradical R (S ⋊⁅ψ⁆ H)) :
    IsNilpotent (envelopingQuotientRep R S ψ J hJ x) := by
  obtain ⟨s, hs, rfl⟩ := Submodule.mem_map.mp (hnr hx)
  rw [LieHom.coe_toLinearMap, SemiDirectSum.inl_eq_mk, envelopingQuotientRep_mk_zero,
    LinearMap.isNilpotent_mulLeft_iff]
  exact hnil s hs

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.RelationModule.Extension
public import TauCeti.Topology.Algebra.GroupExtension.Comparison

/-!
# Lifting a free presentation onto a class-module extension

Let `g : ι → H/W` generate the quotient of a profinite group. A continuous equivariant
surjection from the pro-`p` relation group of `g` to `Wᵃᵇ(p)`, bijective on second
cohomology, gives a surjection from the free profinite group onto the class-module
extension of `H` at `W`, provided the target extension class generates a finite
`p`-power-order cohomology group. The surjection covers the original presentation `lift g`.

No compatibility of the given coefficient map with the extension classes is assumed.
The weak comparison `exists_presentationProfiniteExtension_comparison` detects a
generating source class. The extension comparison theorem
`ProfiniteGroupExtension.exists_surjective_continuousMonoidHom_of_comparison` corrects
the coefficient map by a prime-to-`p` power. Composing the resulting
extension map with the canonical quotient of the free group gives the desired surjection.
This lets a relation-module calculation supply generators for quotients of `H`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  I §5 Exercise 4 and the proof of (7.4.1).
-/

public section

namespace TauCeti.freeProfiniteGroup

open ContCohomology

universe u

variable {p : ℕ} [Fact p.Prime] {ι H : Type u}
  [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [TotallyDisconnectedSpace H]
  {W : Subgroup H} [W.Normal] [IsClosed (W : Set H)]
  {g : ι → H ⧸ W} (hg : Dense (Subgroup.closure (Set.range g) : Set (H ⧸ W)))

/-- A cohomologically bijective surjection from the relation group onto `Wᵃᵇ(p)`
lifts, after a power correction, to a surjection onto the class-module extension.
The projection of the lifted map is the original free presentation. -/
theorem exists_surjective_presentationClassModuleHom :
    letI := presentationClassModuleAction p hg
    letI := continuousSMul_presentationClassModuleAction p hg
    ∀ (f : abelianizationProP p (freeProfiniteGroup ι)
        (lift g : freeProfiniteGroup ι →* H ⧸ W).ker →*[H ⧸ W]
          abelianizationProP p H W)
      (hf : Continuous f),
      Function.Surjective f →
      Function.Bijective (explicitCoeff2 (H ⧸ W)
        (Additive (abelianizationProP p (freeProfiniteGroup ι)
          (lift g : freeProfiniteGroup ι →* H ⧸ W).ker))
        f.toAdditive (f.continuous_toAdditive hf)) →
      AddSubgroup.zmultiples
        (abelianizationProPProfiniteExtension p H W).contCohomologyClass = ⊤ →
      (∃ r : ℕ, Nat.card (H2 (H ⧸ W) (Additive (abelianizationProP p H W))) = p ^ r) →
      ∃ ψ : freeProfiniteGroup ι →ₜ* abelianizationProPExtensionGroup p H W,
        Function.Surjective ψ ∧
          (abelianizationProPExtension p H W).rightHom.comp ψ.toMonoidHom =
            (lift g).toMonoidHom := by
  let := presentationClassModuleAction p hg
  let := continuousSMul_presentationClassModuleAction p hg
  let : IsClosed ((lift g : freeProfiniteGroup ι →* H ⧸ W).ker :
      Set (freeProfiniteGroup ι)) := (lift g).isClosed_ker
  intro f hf hs hc hy hcard
  let X := presentationProfiniteExtension p hg
  let Y := abelianizationProPProfiniteExtension p H W
  obtain ⟨φ, hφ⟩ := exists_presentationProfiniteExtension_comparison p W hg
  obtain ⟨-, χ, -, hχ, -, hright⟩ :=
    X.exists_surjective_continuousMonoidHom_of_comparison Y φ hφ
      isProP_maximalProPQuotient f hf hs hc hy hcard
  let q := ContinuousMonoidHom.quotientMk
    (abelianizationProPExtensionKernel p (freeProfiniteGroup ι)
      (lift g : freeProfiniteGroup ι →* H ⧸ W).ker)
  refine ⟨χ.comp q, hχ.comp QuotientGroup.mk_surjective, MonoidHom.ext fun x ↦ ?_⟩
  have h := DFunLike.congr_fun hright (QuotientGroup.mk x)
  rw [MonoidHom.comp_apply, presentationProfiniteExtension_rightHom_mk] at h
  -- The bundled composition has the canonical quotient carrier; expose its evaluation
  -- because simplification of the carrier hides the quotient-map evaluation lemma.
  change (abelianizationProPExtension p H W).rightHom (χ (QuotientGroup.mk x)) = lift g x
  exact h

end TauCeti.freeProfiniteGroup

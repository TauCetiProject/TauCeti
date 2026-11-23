/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Orbit-quotient descent for pullback vector bundles

Compatibility of `MulAction.orbitRelQuotientRec` with `Bundle.Pullback.lift` for equivariantly
pulled-back linear bundle-map families
(`MulActionHom.lift_totalSpaceMap_pullbackOrbitSection_orbitRelQuotientRec`).
-/

public section

open Bundle TauCeti

namespace MulActionHom

variable {G M G' M' 𝕜 F₁ F₂ : Type*} [Group G] [MulAction G M] [Group G'] [MulAction G' M']
  [Semiring 𝕜] {V W : MulAction.orbitRel.Quotient G M → Type*}
  [∀ q, AddCommMonoid (V q)] [∀ q, Module 𝕜 (V q)] [∀ q, TopologicalSpace (V q)]
  [∀ q, AddCommMonoid (W q)] [∀ q, Module 𝕜 (W q)] [∀ q, TopologicalSpace (W q)]
  {σ : G' → G} (ψ : M' →ₑ[σ] M)
  {φ : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x) →L[𝕜]
    W (Quotient.mk (MulAction.orbitRel G M) x)}
  (hφ : ∀ (g : G) (x : M), φ (g • x) ≍ φ x)

/-- On total spaces, the `G'`-descent of the equivariant pullback of `φ` intertwines with the
`G`-descent of `φ` along `Pullback.lift ψ.orbitRelQuotientMap`. -/
theorem lift_totalSpaceMap_pullbackOrbitSection_orbitRelQuotientRec
    (p : TotalSpace F₁ (ψ.orbitRelQuotientMap *ᵖ V)) :
    Pullback.lift ψ.orbitRelQuotientMap (TotalSpace.mk' F₂ (E := ψ.orbitRelQuotientMap *ᵖ W) p.proj
        (MulAction.orbitRelQuotientRec
          (V := fun q' ↦ (ψ.orbitRelQuotientMap *ᵖ V) q' →L[𝕜] (ψ.orbitRelQuotientMap *ᵖ W) q')
          (ψ.pullbackOrbitSection (V := fun q ↦ V q →L[𝕜] W q) φ)
          (ψ.pullbackOrbitSection_smul_heq (V := fun q ↦ V q →L[𝕜] W q) hφ) p.proj p.snd)) =
      TotalSpace.mk' F₂ (ψ.orbitRelQuotientMap p.proj)
        (MulAction.orbitRelQuotientRec (V := fun q ↦ V q →L[𝕜] W q) φ hφ
          (ψ.orbitRelQuotientMap p.proj) p.snd) :=
  congrArg (fun T : V (ψ.orbitRelQuotientMap p.proj) →L[𝕜] W (ψ.orbitRelQuotientMap p.proj) ↦
      TotalSpace.mk' F₂ (ψ.orbitRelQuotientMap p.proj) (T p.snd))
    (ψ.orbitRelQuotientRec_pullbackOrbitSection (V := fun q ↦ V q →L[𝕜] W q) hφ p.proj)

end MulActionHom

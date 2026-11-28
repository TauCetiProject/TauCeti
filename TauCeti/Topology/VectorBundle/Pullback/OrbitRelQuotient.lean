/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient.Operations
public import TauCeti.Topology.VectorBundle.Pullback

/-!
# Orbit-quotient descent for pullback vector bundles

Equivariant pullbacks of upstairs sections along `MulActionHom.orbitRelQuotientMap`
(`MulActionHom.pullbackOrbitSection`, `MulActionHom.orbitRelQuotientRec_pullbackOrbitSection`,
`MulActionHom.lift_pullbackOrbitSection`), and compatibility of `MulAction.orbitRelQuotientRec`
with `Bundle.Pullback.lift` for equivariantly pulled-back linear bundle-map families
(`MulActionHom.lift_totalSpaceMap_pullbackOrbitSection_orbitRelQuotientRec`).
-/

public section

open Bundle TauCeti

namespace MulActionHom

section PullbackSection

variable {G' M' G M : Type*} [Group G'] [MulAction G' M'] [Group G] [MulAction G M]
  {σ : G' → G} (ψ : M' →ₑ[σ] M) {V : MulAction.orbitRel.Quotient G M → Type*}
  (t : ∀ x : M, V (Quotient.mk (MulAction.orbitRel G M) x))

/-- Pullback of an upstairs family `t : ∀ x : M, V ⟦x⟧` along a `σ`-equivariant map
`ψ : M' →ₑ[σ] M`, viewed as an upstairs family on `M'` for `ψ.orbitRelQuotientMap *ᵖ V`. -/
def pullbackOrbitSection (x' : M') :
    (ψ.orbitRelQuotientMap *ᵖ V) (Quotient.mk (MulAction.orbitRel G' M') x') :=
  cast (congrArg V (ψ.orbitRelQuotientMap_mk x').symm) (t (ψ x'))

/-- `ψ.pullbackOrbitSection t x'` is heterogeneously equal to `t (ψ x')`. -/
@[simp] theorem pullbackOrbitSection_heq (x' : M') :
    ψ.pullbackOrbitSection t x' ≍ t (ψ x') := cast_heq _ _

variable {t}

/-- If `t` is `G`-invariant, `ψ.pullbackOrbitSection t` is `G'`-invariant. -/
theorem pullbackOrbitSection_smul_heq
    (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x) (g' : G') (x' : M') :
    ψ.pullbackOrbitSection t (g' • x') ≍ ψ.pullbackOrbitSection t x' :=
  ψ.smul_heq_of_comp_orbitRelQuotientMap ht (ψ.pullbackOrbitSection_heq t) g' x'

/-- **Section descent commutes with equivariant pullback.** Descending `ψ.pullbackOrbitSection t`
to `M' ⧸ G'` produces the pullback along `ψ.orbitRelQuotientMap` of the descent on `M ⧸ G`. -/
theorem orbitRelQuotientRec_pullbackOrbitSection
    (ht : ∀ (g : G) (x : M), t (g • x) ≍ t x) (q' : MulAction.orbitRel.Quotient G' M') :
    MulAction.orbitRelQuotientRec (V := ψ.orbitRelQuotientMap *ᵖ V)
        (ψ.pullbackOrbitSection t) (ψ.pullbackOrbitSection_smul_heq ht) q' =
      MulAction.orbitRelQuotientRec t ht (ψ.orbitRelQuotientMap q') :=
  (ψ.orbitRelQuotientRec_orbitRelQuotientMap_apply ht (ψ.pullbackOrbitSection_heq t) q').symm

/-- Lifting `ψ.pullbackOrbitSection t x'` to `TotalSpace F V` recovers `(⟦ψ x'⟧, t (ψ x'))`. -/
@[simp] theorem lift_pullbackOrbitSection (F : Type*) (t) (x' : M') :
    Pullback.lift ψ.orbitRelQuotientMap (TotalSpace.mk' F (E := ψ.orbitRelQuotientMap *ᵖ V)
        (Quotient.mk (MulAction.orbitRel G' M') x') (ψ.pullbackOrbitSection t x')) =
      TotalSpace.mk' F (Quotient.mk (MulAction.orbitRel G M) (ψ x')) (t (ψ x')) :=
  TotalSpace.mk_cast (ψ.orbitRelQuotientMap_mk x').symm (t (ψ x'))

end PullbackSection

section TotalSpaceMap

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

end TotalSpaceMap

end MulActionHom

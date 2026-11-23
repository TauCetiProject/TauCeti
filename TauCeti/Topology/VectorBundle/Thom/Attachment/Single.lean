/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.Attachment

/-!
# Attaching a single disc bundle and its Thom-pair homology and cohomology

Let `E → B` be a real vector bundle equipped with a fibre gauge `ρ : TotalSpace F E → ℝ`
(`TauCeti.IsFiberGauge`), with disc bundle `D_ρ(E) = {ρ ≤ 1}` and sphere bundle `S_ρ(E) = {ρ = 1}`
(`TauCeti.gaugeDiscBundle`, `TauCeti.gaugeSphereBundle`). Examples include the unit fibre norm
(`TauCeti.isFiberGauge_norm`), any rescaling of a fibre gauge by a continuous positive radius
function `r : B → ℝ` on the base (`TauCeti.IsFiberGauge.div_comp_proj`), and square roots of
continuous positive-definite quadratic forms such as Morse–Bott normal Hessians
(`TauCeti.isFiberGauge_sqrt`).

If a space `Z` is obtained from a closed subset `X` by attaching `D_ρ(E)` along `S_ρ(E)` through a
closed embedding `f : (D_ρ(E), S_ρ(E)) ⟶ (Z, X)`, then `f` induces isomorphisms on relative
singular homology and cohomology (`TauCeti.isIso_singularHomologyMap_of_attach_gaugeDiscBundle`,
`TauCeti.isIso_singularCohomologyMap_of_attach_gaugeDiscBundle`). Composing with the comparison
`(D_ρ(E), S_ρ(E)) ⟶ (E, E₀)` (`TauCeti.isIso_singularHomologyMap_gaugeDiscSpherePairMap`,
`TauCeti.isIso_singularCohomologyMap_gaugeDiscSpherePairMap`) yields the Thom-pair identifications
`Hₙ(E, E₀) ≅ Hₙ(Z, X)` and `Hⁿ(Z, X) ≅ Hⁿ(E, E₀)`
(`TauCeti.singularHomologyIsoThomPairOfAttachGaugeDiscBundle`,
`TauCeti.singularCohomologyIsoThomPairOfAttachGaugeDiscBundle`).
-/

public section

noncomputable section

open Bundle CategoryTheory Limits Set Topology

universe uF w v u

namespace TauCeti

variable {B : Type w} {F : Type uF} {E : B → Type w} [TopologicalSpace B]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [∀ b, AddCommGroup (E b)] [∀ b, Module ℝ (E b)]
  [∀ b, TopologicalSpace (E b)] [TopologicalSpace (TotalSpace F E)] [FiberBundle F E]
  [VectorBundle ℝ F E] {ρ : TotalSpace F E → ℝ} (hρ : IsFiberGauge ρ)
  {Z : Type w} [TopologicalSpace Z] {X : Set Z}
  {f : gaugeDiscSpherePair ρ ⟶ TopPair.ofSubset (X := TopCat.of Z) X}
  (hf : IsClosedEmbedding (TopPair.Hom.fst f)) (hX : IsClosed X)
  (hfX : ∀ v : gaugeDiscBundle ρ,
    TopPair.Hom.fst f v ∈ X → (v : TotalSpace F E) ∈ gaugeSphereBundle ρ)
  (hfcover : X ∪ range (TopPair.Hom.fst f) = univ)
  {C : Type u} [Category.{v} C] [HasCoproducts.{w} C] [Abelian C]

/-- **Thom-pair homology of a single gauge disc-bundle attachment**: `Hₙ(E, E₀) ≅ Hₙ(Z, X)`, formed
from the zig-zag `(E, E₀) ← (D_ρ(E), S_ρ(E)) → (Z, X)`. -/
def singularHomologyIsoThomPairOfAttachGaugeDiscBundle (R : C) (n : ℕ) :
    (thomPair F E).singularHomology R n ≅
      (TopPair.ofSubset (X := TopCat.of Z) X).singularHomology R n :=
  (@asIso _ _ _ _ (TopPair.singularHomologyMap (gaugeDiscSpherePairMap hρ) R n)
    (isIso_singularHomologyMap_gaugeDiscSpherePairMap hρ R n)).symm ≪≫
  @asIso _ _ _ _ (TopPair.singularHomologyMap f R n)
    (isIso_singularHomologyMap_of_attach_gaugeDiscBundle hρ hX R n hf hfX hfcover)

@[reassoc (attr := simp)]
theorem singularHomologyMap_gaugeDiscSpherePairMap_comp_isoThomPair_hom (R : C) (n : ℕ) :
    TopPair.singularHomologyMap (gaugeDiscSpherePairMap hρ) R n ≫
        (singularHomologyIsoThomPairOfAttachGaugeDiscBundle
          hρ hf hX hfX hfcover R n).hom =
      TopPair.singularHomologyMap f R n := by
  have := isIso_singularHomologyMap_gaugeDiscSpherePairMap hρ R n
  have := isIso_singularHomologyMap_of_attach_gaugeDiscBundle hρ hX R n hf hfX hfcover
  simp [singularHomologyIsoThomPairOfAttachGaugeDiscBundle]

@[reassoc (attr := simp)]
theorem singularHomologyMap_attach_comp_isoThomPair_inv (R : C) (n : ℕ) :
    TopPair.singularHomologyMap f R n ≫
        (singularHomologyIsoThomPairOfAttachGaugeDiscBundle
          hρ hf hX hfX hfcover R n).inv =
      TopPair.singularHomologyMap (gaugeDiscSpherePairMap hρ) R n := by
  have := isIso_singularHomologyMap_gaugeDiscSpherePairMap hρ R n
  have := isIso_singularHomologyMap_of_attach_gaugeDiscBundle hρ hX R n hf hfX hfcover
  simp [singularHomologyIsoThomPairOfAttachGaugeDiscBundle]

/-- **Thom-pair cohomology of a single gauge disc-bundle attachment**: `Hⁿ(Z, X) ≅ Hⁿ(E, E₀)`,
formed from the zig-zag `(E, E₀) ← (D_ρ(E), S_ρ(E)) → (Z, X)`. -/
def singularCohomologyIsoThomPairOfAttachGaugeDiscBundle
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (TopPair.ofSubset (X := TopCat.of Z) X).singularCohomology R k M n ≅
      (thomPair F E).singularCohomology R k M n :=
  @asIso _ _ _ _ (TopPair.singularCohomologyMap (R := R) (k := k) (M := M) f n)
    (isIso_singularCohomologyMap_of_attach_gaugeDiscBundle hρ hX R n k M hf hfX hfcover) ≪≫
  (@asIso _ _ _ _ (TopPair.singularCohomologyMap (R := R) (k := k) (M := M)
      (gaugeDiscSpherePairMap hρ) n)
    (isIso_singularCohomologyMap_gaugeDiscSpherePairMap hρ R k M n)).symm

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairOfAttachGaugeDiscBundle_hom_comp
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (singularCohomologyIsoThomPairOfAttachGaugeDiscBundle
        hρ hf hX hfX hfcover R k M n).hom ≫
      TopPair.singularCohomologyMap (gaugeDiscSpherePairMap hρ) n =
      TopPair.singularCohomologyMap f n := by
  have := isIso_singularCohomologyMap_gaugeDiscSpherePairMap hρ R k M n
  have := isIso_singularCohomologyMap_of_attach_gaugeDiscBundle hρ hX R n k M hf hfX hfcover
  simp [singularCohomologyIsoThomPairOfAttachGaugeDiscBundle]

@[reassoc (attr := simp)]
theorem singularCohomologyIsoThomPairOfAttachGaugeDiscBundle_inv_comp
    (R : C) (k : Type*) [Ring k] [Linear k C] (M : C) (n : ℕ) :
    (singularCohomologyIsoThomPairOfAttachGaugeDiscBundle
        hρ hf hX hfX hfcover R k M n).inv ≫
      TopPair.singularCohomologyMap f n =
      TopPair.singularCohomologyMap (gaugeDiscSpherePairMap hρ) n := by
  have := isIso_singularCohomologyMap_gaugeDiscSpherePairMap hρ R k M n
  have := isIso_singularCohomologyMap_of_attach_gaugeDiscBundle hρ hX R n k M hf hfX hfcover
  simp [singularCohomologyIsoThomPairOfAttachGaugeDiscBundle]

end TauCeti

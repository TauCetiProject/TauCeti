/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Transfer.Basic
public import Mathlib.Topology.Instances.ZMod
import TauCeti.RepresentationTheory.Homological.ContCohomology.Bockstein.Integral
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Corestriction
import TauCeti.RepresentationTheory.Homological.ContCohomology.Corestriction.Transfer
import TauCeti.Topology.Algebra.Group.Profinite.ProP.Character.Separation
import TauCeti.Topology.Algebra.Group.TopologicalAbelianization.Lift

/-!
# The transfer to the pro-p class module in strict cohomological dimension two

Let `G` be a profinite group with `scd_p G ≤ 2` and let `V` be an open subgroup. The transfer
`Ver : G → V^ab(p)` (`TauCeti.abelianizationProPTransfer`) has the same kernel as the canonical map
`G → G^ab(p)`, so it induces an injection `G^ab(p) → V^ab(p)`. This is the injectivity half of
NSW (3.6.4)(ii) in `p`-primary form.

One inclusion needs no hypothesis on `G` beyond profiniteness: `Ver` is a continuous homomorphism
to the abelian pro-`p` group `V^ab(p)`, so it factors through `G^ab(p)`
(`TauCeti.abelianizationProPTransfer_eq_one_of_mk_eq_one`). The other inclusion is
NSW (3.3.11) in degree `2` with coefficients `ℤ`, read on characters. A continuous character
`χ : G → ℤ/p^k` has a `p`-primary integral Bockstein `δχ ∈ H²(G, ℤ)`. Because `scd_p G ≤ 2`,
`δχ` is a corestriction from `H²(V, ℤ)`, so it is the corestriction of the Bockstein `δψ` of a
character `ψ` of `V`. Corestriction commutes with the Bockstein, and on characters it is the
transfer (NSW (1.5.9)), so `δχ = δ(ψ ∘ Ver)`. Moving both characters to a common modulus, and
using that the degree-one Bockstein is injective, gives `χ = ψ ∘ Ver` up to a multiplication of
the coefficients. So `χ` kills the kernel of `Ver` (`TauCeti.zmodChar_eq_one_of_transfer_eq_one`).
Finally, continuous characters into the groups `ℤ/p^k` separate the points of the abelian pro-`p`
group `G^ab(p)` (`TauCeti.exists_continuous_zmodChar_of_notMem`).

The subgroup `V` need not be normal.

## Main results

* `TauCeti.zmodChar_eq_one_of_transfer_eq_one`: under `scd_p G ≤ 2`, a continuous character of `G`
  of `p`-power order kills the kernel of the transfer.
* `TauCeti.abelianizationProPTransfer_eq_one_iff`: under `scd_p G ≤ 2`, the kernel of the transfer
  is the kernel of `G → G^ab(p)`.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed., (1.5.9),
  (3.3.11) and the proof of (3.6.4), (i) ⇒ (ii).
-/

public section

namespace TauCeti

open CategoryTheory ContCohomology _root_.TauCeti.ContinuousCohomology

universe u

attribute [local instance 2000] Ring.toAddCommGroup
attribute [local instance] trivialZModAction integralAction integralContinuousSMul
  cyclicContinuousSMul

section Characters

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The class in `H¹(G, ℤ/n)` of a continuous character, through the trivial-action description
of the explicit `H¹`. -/
private noncomputable def charClass (n : ℕ) :
    Additive (G →ₜ* Multiplicative (ULift.{u} (ZMod n))) ≃+
      continuousCohomology 1 (ofDiscreteModule ℤ G (ULift.{u} (ZMod n))) :=
  (H1EquivOfSmulEqSelf (G := G) (M := ULift.{u} (ZMod n)) fun _ _ ↦ rfl).symm.trans
    (explicitH1AddEquivContinuousCohomology G (ULift.{u} (ZMod n)))

/-- The coefficient map of a homomorphism `f : ℤ/n → ℤ/m` acts on characters by composition
with `f`. -/
private theorem charClass_symm_coeffMap_apply {n m : ℕ} (f : ZMod n →+ ZMod m)
    (x : continuousCohomology 1 (ofDiscreteModule ℤ G (ULift.{u} (ZMod n)))) (g : G) :
    Multiplicative.toAdd (Additive.toMul ((charClass G m).symm
      (coeffMap (ofDiscreteModuleMap ((AddEquiv.ulift.symm.toAddMonoidHom.comp f).comp
        AddEquiv.ulift.toAddMonoidHom).toIntLinearMap fun _ _ ↦ rfl) 1 x)) g) =
      ULift.up (f (Multiplicative.toAdd (Additive.toMul ((charClass G n).symm x) g)).down) := by
  obtain ⟨χ, rfl⟩ := (charClass G n).surjective x
  let F : ULift.{u} (ZMod n) →+[G] ULift.{u} (ZMod m) :=
    { (AddEquiv.ulift.symm.toAddMonoidHom.comp f).comp AddEquiv.ulift.toAddMonoidHom with
      map_smul' := fun _ _ ↦ rfl }
  have h := explicitH1AddEquivContinuousCohomology_coeffMap G (ULift.{u} (ZMod n))
    (ULift.{u} (ZMod m)) F ((H1EquivOfSmulEqSelf (G := G) (M := ULift.{u} (ZMod n))
      fun _ _ ↦ rfl).symm χ)
  -- `h` states the comparison for the coefficient map of the bundled equivariant map `F`, whose
  -- underlying additive map is the composite in the statement; restate it in that form.
  change coeffMap (ofDiscreteModuleMap ((AddEquiv.ulift.symm.toAddMonoidHom.comp f).comp
    AddEquiv.ulift.toAddMonoidHom).toIntLinearMap fun _ _ ↦ rfl) 1 (charClass G n χ) = _ at h
  rw [h]
  simp [charClass]
  -- What is left evaluates the bundled `F`, whose value is the composite
  -- `ULift.up ∘ f ∘ ULift.down` by construction; Mathlib has no `coe_mk` lemma for
  -- `DistribMulActionHom` to rewrite with.
  rfl

variable [CompactSpace G] [TotallyDisconnectedSpace G]

/-- Degree-one corestriction with trivial coefficients `ℤ/n` is the transfer of characters
(NSW (1.5.9)). -/
private theorem corestriction_charClass {V : Subgroup G} [V.FiniteIndex] (hV : IsOpen (V : Set G))
    {n : ℕ} (ψ : V →ₜ* Multiplicative (ULift.{u} (ZMod n))) :
    corestriction V (ULift.{u} (ZMod n)) hV 1 (charClass V n (Additive.ofMul ψ)) =
      charClass G n (Additive.ofMul
        ⟨MonoidHom.transfer ψ.toMonoidHom, continuous_transfer hV ψ.continuous⟩) := by
  have h := explicitH1AddEquivContinuousCohomology_corestriction V (ULift.{u} (ZMod n)) hV
    ((H1EquivOfSmulEqSelf (G := V) (M := ULift.{u} (ZMod n)) fun _ _ ↦ rfl).symm
      (Additive.ofMul ψ))
  refine h.trans (congrArg _ ((H1EquivOfSmulEqSelf (G := G) (M := ULift.{u} (ZMod n))
    fun _ _ ↦ rfl).symm_apply_eq.2 ?_)).symm
  apply Additive.toMul.injective
  refine ContinuousMonoidHom.ext fun g ↦ ?_
  have := DFunLike.congr_fun (H1EquivOfSmulEqSelf_explicitCor1_eq_transfer
    (G := G) (M := ULift.{u} (ZMod n)) (fun _ _ ↦ rfl) hV
    ((H1EquivOfSmulEqSelf (G := V) (M := ULift.{u} (ZMod n)) fun _ _ ↦ rfl).symm
      (Additive.ofMul ψ))) g
  rw [AddEquiv.apply_symm_apply] at this
  exact this.symm

end Characters

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {V : Subgroup G} [V.FiniteIndex]

omit [TotallyDisconnectedSpace G] in
/-- The transfer of a continuous character `ψ : V → ℤ/p^m` kills the kernel of the transfer
`G → V^ab(p)`, because `ψ` factors through `V^ab(p)`. -/
private theorem transfer_apply_eq_one [NeZero p] (hV : IsOpen (V : Set G)) {m : ℕ}
    (ψ : V →ₜ* Multiplicative (ULift.{u} (ZMod (p ^ m)))) {g : G}
    (hg : abelianizationProPTransfer p G V g = 1) :
    MonoidHom.transfer ψ.toMonoidHom g = 1 := by
  have : CompactSpace V := isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  have hP : IsProP p (Multiplicative (ULift.{u} (ZMod (p ^ m)))) :=
    ((ZModModule.isPGroup_multiplicative (n := p ^ m) (G := ZMod (p ^ m))).of_pow.of_equiv
      AddEquiv.ulift.symm.toMultiplicative).isProP
  let ψab := TopologicalAbelianization.lift ψ
  let ψ' := maximalProPQuotient.lift hP ψab.toMonoidHom ψab.continuous
  have hψ : ψ.toMonoidHom = ψ'.comp (abelianizationProPMk p G V) := by
    ext v
    simp [ψ', ψab, abelianizationProPMk_apply]
  rw [hψ, MonoidHom.transfer_comp, MonoidHom.comp_apply, ← abelianizationProPTransfer_def, hg,
    map_one]

/-- **A character of `p`-power order dies on the kernel of the transfer.** For a profinite
group `G` with `scd_p G ≤ 2` and an open subgroup `V`, every continuous character
`χ : G → ℤ/p^k` is trivial on the kernel of the transfer `Ver : G → V^ab(p)`. This is NSW
(3.3.11) at `n = 2` with integral coefficients, read on characters through the integral
Bockstein maps and (1.5.9). -/
theorem zmodChar_eq_one_of_transfer_eq_one (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) (hV : IsOpen (V : Set G)) {k : ℕ}
    (χ : G →* Multiplicative (ZMod (p ^ k))) (hχ : Continuous χ) {g : G}
    (hg : abelianizationProPTransfer p G V g = 1) : χ g = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : CompactSpace V := isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  -- The class `c ∈ H¹(G, ℤ/p^k)` of `χ`, and its integral Bockstein, a `p`-primary class.
  let up : Multiplicative (ZMod (p ^ k)) →* Multiplicative (ULift.{u} (ZMod (p ^ k))) :=
    AddEquiv.ulift.symm.toMultiplicative.toMonoidHom
  have hup : Continuous up := continuous_of_discreteTopology
  let χ' : G →ₜ* Multiplicative (ULift.{u} (ZMod (p ^ k))) := ⟨up.comp χ, hup.comp hχ⟩
  set c := charClass G (p ^ k) (Additive.ofMul χ') with hc
  have hx : integralBockstein G (p ^ k) 1 c ∈ AddCommGroup.primaryComponent _ p :=
    (mem_primaryComponent_iff_exists_integralBockstein G p _).2 ⟨k, c, rfl⟩
  -- It is the corestriction of a `p`-primary class of `H²(V, ℤ)`, the Bockstein of a character
  -- `ψ` of `V`; so it is the Bockstein of the transfer of `ψ`.
  obtain ⟨y, hy, hyx⟩ := corestriction_surjOn_primaryComponent_of_strictCohomologicalDimensionAt_le
    hp h hV (ULift.{u} ℤ) hx
  obtain ⟨m, d, rfl⟩ := (mem_primaryComponent_iff_exists_integralBockstein V p y).1 hy
  obtain ⟨ψ, rfl⟩ := (charClass V (p ^ m)).surjective d
  let ψT : G →ₜ* Multiplicative (ULift.{u} (ZMod (p ^ m))) :=
    ⟨MonoidHom.transfer (Additive.toMul ψ).toMonoidHom,
      continuous_transfer hV (Additive.toMul ψ).continuous⟩
  have h₁ : integralBockstein G (p ^ m) 1 (charClass G (p ^ m) (Additive.ofMul ψT)) =
      integralBockstein G (p ^ k) 1 c := by
    rw [← hyx, ← corestriction_charClass G hV (Additive.toMul ψ)]
    exact ConcreteCategory.congr_hom
      (integralBockstein_corestriction G (p ^ m) V hV 1) (charClass V (p ^ m) ψ)
  -- Raised to the common modulus `p ^ (k + m)`, the two characters have the same Bockstein,
  -- hence agree, the degree-one Bockstein being injective.
  have hN₁ : p ^ k * p ^ m = p ^ (k + m) := (pow_add p k m).symm
  have hN₂ : p ^ m * p ^ k = p ^ (k + m) := by rw [mul_comm, pow_add]
  have hB {a b : ℕ} [NeZero a] (hab : a * b = p ^ (k + m))
      (x : continuousCohomology 1 (ofDiscreteModule ℤ G (ULift.{u} (ZMod a)))) :
      integralBockstein G (p ^ (k + m)) 1 (coeffMap (ofDiscreteModuleMap
        ((AddEquiv.ulift.symm.toAddMonoidHom.comp (ZMod.mulCastHom b hab)).comp
          AddEquiv.ulift.toAddMonoidHom).toIntLinearMap fun _ _ ↦ rfl) 1 x) =
        integralBockstein G a 1 x := by
    rw [← ConcreteCategory.comp_apply, integralBockstein_mulCastHom]
  have h₂ := integralBockstein_one_injective G (p ^ (k + m))
    ((hB hN₁ c).trans (h₁.symm.trans (hB hN₂ _).symm))
  have h₃ := congrArg (fun x ↦ (Multiplicative.toAdd
    (Additive.toMul ((charClass G (p ^ (k + m))).symm x) g)).down) h₂
  simp only [charClass_symm_coeffMap_apply, hc, AddEquiv.symm_apply_apply] at h₃
  -- The transfer of `ψ` kills `g`, so the raised value of `χ g` vanishes.
  have hψg : ψT g = 1 :=
    transfer_apply_eq_one hV (Additive.toMul ψ) hg
  -- `χ'` is `χ` followed by the lift `ZMod (p ^ k) ≃+ ULift (ZMod (p ^ k))`.
  have hχg : (Multiplicative.toAdd (χ' g)).down = Multiplicative.toAdd (χ g) := rfl
  rw [toMul_ofMul, toMul_ofMul, hψg, hχg, toAdd_one, ULift.zero_down, _root_.map_zero] at h₃
  rw [← toAdd_eq_zero]
  exact ZMod.mulCastHom_injective (p ^ m) hN₁ (pow_ne_zero m hp.ne_zero)
    (h₃.trans (_root_.map_zero _).symm)

/-- **The kernel of the transfer** (NSW (3.6.4)(ii), injectivity, in `p`-primary form). For a
profinite group `G` with `scd_p G ≤ 2` and an open subgroup `V`, an element of `G` dies under the
transfer `Ver : G → V^ab(p)` exactly when it dies in `G^ab(p)`. So `Ver` induces an injection
`G^ab(p) → V^ab(p)`. The prime `p` is needed only for the forward direction. -/
theorem abelianizationProPTransfer_eq_one_iff (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) (hV : IsOpen (V : Set G)) (g : G) :
    abelianizationProPTransfer p G V g = 1 ↔
      maximalProPQuotient.mk p (TopologicalAbelianization G)
        (g : TopologicalAbelianization G) = 1 := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have : CompactSpace V := isCompact_iff_compactSpace.mp (V.isClosed_of_isOpen hV).isCompact
  let π : G →* maximalProPQuotient p (TopologicalAbelianization G) :=
    (maximalProPQuotient.mk p (TopologicalAbelianization G)).comp
      (QuotientGroup.mk' (commutator G).topologicalClosure)
  have hπ : Continuous π :=
    (maximalProPQuotient.continuous_mk (p := p) (G := TopologicalAbelianization G)).comp
      QuotientGroup.continuous_mk
  constructor
  · -- A character of `G^ab(p)` separating the class of `g` from `1` would be a character of `G`
    -- not killing `g`.
    intro hg
    by_contra hne
    obtain ⟨k, χ, hχ, -, hχg⟩ := exists_continuous_zmodChar_of_notMem
      (isProP_maximalProPQuotient (p := p) (G := TopologicalAbelianization G)) ⊥
      (by rw [Subgroup.coe_bot]; exact isClosed_singleton) (π g)
      (Subgroup.mem_bot.not.mpr hne)
    exact hχg (zmodChar_eq_one_of_transfer_eq_one hp h hV (χ.comp π) (hχ.comp hπ) hg)
  · exact abelianizationProPTransfer_eq_one_of_mk_eq_one hV

end TauCeti

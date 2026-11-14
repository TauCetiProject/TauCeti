/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Crystal.WeightTwist
public import TauCeti.RepresentationTheory.LSPath.Central.Transport
public import TauCeti.RepresentationTheory.LSPath.Crystal
import TauCeti.LinearAlgebra.RootSystem.Reduced
import TauCeti.RepresentationTheory.LSPath.OrbitStable

/-!
# Central transport as a strict isomorphism of Lakshmibai–Seshadri path crystals

Let `P : RootDatum ι X Y` be a reduced root datum with finite index type and base `b`, let `λ : X`
be a dominant weight, and let `χ : X` be a central weight (annihilated by every simple coroot).
Adding the linear path `t ↦ t χ` is not well-defined on arbitrary reparametrization classes of
piecewise-linear paths (`TauCeti.PLPath.not_exists_shiftTimed_on_paths`), so
`TauCeti.LSPath.centralTransport` applies the shear to the canonical distinguished presentation
`TauCeti.LSPath.timed` with slopes in `W λ`.

This file proves that `TauCeti.LSPath.centralTransport` intertwines the Kashiwara root operators of
`TauCeti.LSPath.crystal`, shifts weights by `χ`, and preserves string lengths, using
`TauCeti.PLPath.lower_ofSegments_shiftTimed` and `TauCeti.PLPath.distinguished_of_lower_eq_some`.
For central weights `χ, σ : X`, we package this into the strict crystal isomorphism
`TauCeti.LSPath.centralTransportIso` (`B(λ)^(σ + χ) ≃ B(λ + χ)^σ`) and its `σ = 0` specialization
`TauCeti.LSPath.centralTransportIsoZero` (`B(λ)^χ ≃ B(λ + χ)`), prove the strict-map identity,
additive composition, and inverse coherence laws, and identify pure-central LS path crystals (in
particular for `0`) with `TauCeti.NormalCrystal.central` (`TauCeti.LSPath.centralIso`,
`TauCeti.LSPath.zeroIso`).

## Main definitions and results

* `TauCeti.NormalCrystal.StrictIso.weightTwist`, `TauCeti.NormalCrystal.StrictIso.congrLeft`, and
  `TauCeti.NormalCrystal.StrictIso.congrRight`.
* `TauCeti.LSPath.centralTransport_zero`, `TauCeti.LSPath.centralTransport_centralTransport`,
  `TauCeti.LSPath.centralTransport_symm_apply`, and
  `TauCeti.LSPath.eq_straight_of_forall_coroot'_eq_zero`.
* `TauCeti.LSPath.centralTransportIso`, `TauCeti.LSPath.centralTransportIsoZero`,
  `TauCeti.LSPath.centralTransportIso_zero`,
  `TauCeti.LSPath.centralTransportIso_trans_centralTransportIso`, and
  `TauCeti.LSPath.centralTransportIso_symm`.
* `TauCeti.LSPath.centralIso` and `TauCeti.LSPath.zeroIso`.

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), 329--346, Section 4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  499--525, Section 4.
* M. Kashiwara, *On crystal bases*, CMS Conf. Proc. 16 (1995), §7.
-/

public section

namespace TauCeti

/-! ### Central weight twists and equality casts on strict crystal isomorphisms -/

namespace NormalCrystal

variable {ι X Y B B' B'' : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base}

/-- Equal central offsets produce equal weight-twisted crystals. -/
theorem weightTwist_congr (c : NormalCrystal P b B) {χ₁ χ₂ : X} (h : χ₁ = χ₂)
    (hχ₁ : ∀ i : b.support, P.toLinearMap χ₁ (P.coroot i) = 0)
    (hχ₂ : ∀ i : b.support, P.toLinearMap χ₂ (P.coroot i) = 0) :
    c.weightTwist χ₁ hχ₁ = c.weightTwist χ₂ hχ₂ := by subst h; rfl

namespace StrictIso

variable {c : NormalCrystal P b B} {d : NormalCrystal P b B'} {d' : NormalCrystal P b B''}

/-- Replace the source of a strict crystal isomorphism along an equality of normal crystals on the
same carrier. -/
def congrLeft {c₁ c₂ : NormalCrystal P b B} (h : c₁ = c₂) (ψ : StrictIso c₁ d) :
    StrictIso c₂ d where
  toEquiv := ψ.toEquiv
  wt_toFun x := by subst h; exact ψ.wt_toFun x
  e_toFun i x := by subst h; exact ψ.e_toFun i x

@[simp]
theorem coe_congrLeft {c₁ c₂ : NormalCrystal P b B} (h : c₁ = c₂) (ψ : StrictIso c₁ d) :
    ⇑(ψ.congrLeft h) = ψ :=
  (rfl)

/-- Replace the target of a strict crystal isomorphism along an equality of normal crystals on the
same carrier. -/
def congrRight {d₁ d₂ : NormalCrystal P b B'} (h : d₁ = d₂) (ψ : StrictIso c d₁) :
    StrictIso c d₂ where
  toEquiv := ψ.toEquiv
  wt_toFun x := by subst h; exact ψ.wt_toFun x
  e_toFun i x := by subst h; exact ψ.e_toFun i x

@[simp]
theorem coe_congrRight {d₁ d₂ : NormalCrystal P b B'} (h : d₁ = d₂) (ψ : StrictIso c d₁) :
    ⇑(ψ.congrRight h) = ψ :=
  (rfl)

/-- Twist the source and target of a strict crystal isomorphism by the same central weight. -/
def weightTwist (ψ : StrictIso c d) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    StrictIso (c.weightTwist χ hχ) (d.weightTwist χ hχ) where
  toEquiv := ψ.toEquiv
  wt_toFun x := by simp
  e_toFun i x := by simp

@[simp]
theorem coe_weightTwist (ψ : StrictIso c d) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    ⇑(ψ.weightTwist χ hχ) = ψ :=
  (rfl)

@[simp]
theorem weightTwist_refl (c : NormalCrystal P b B) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    (StrictIso.refl c).weightTwist χ hχ = StrictIso.refl (c.weightTwist χ hχ) :=
  StrictIso.ext fun _ ↦ by simp

@[simp]
theorem weightTwist_symm (ψ : StrictIso c d) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    (ψ.weightTwist χ hχ).symm = ψ.symm.weightTwist χ hχ :=
  StrictIso.ext fun y ↦ by
    obtain ⟨x, rfl⟩ := ψ.toEquiv.surjective y
    exact ((ψ.weightTwist χ hχ).symm_apply_apply x).trans (ψ.symm_apply_apply x).symm

@[simp]
theorem weightTwist_trans (ψ : StrictIso c d) (φ : StrictIso d d') (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0) :
    (ψ.trans φ).weightTwist χ hχ = (ψ.weightTwist χ hχ).trans (φ.weightTwist χ hχ) :=
  StrictIso.ext fun _ ↦ by simp

end StrictIso

end NormalCrystal

/-! ### Dominance of central weights -/

open RootPairing

/-- A weight killed by every simple coroot lies in the closed dominant chamber. -/
theorem mem_dominantChamber_of_forall_coroot'_eq_zero {ι R M N : Type*} [CommRing R]
    [LinearOrder R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    {P : RootPairing ι R M N} {b : P.Base} {χ : M}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) :
    χ ∈ dominantChamber P b :=
  (mem_dominantChamber P b χ).mpr fun i hi ↦ (hχ i hi).ge

/-- Adding a weight killed by every simple coroot preserves membership in the closed dominant
chamber. -/
theorem add_mem_dominantChamber_of_forall_coroot'_eq_zero {ι R M N : Type*} [CommRing R]
    [LinearOrder R] [IsOrderedAddMonoid R] [AddCommGroup M] [AddCommGroup N] [Module R M]
    [Module R N] {P : RootPairing ι R M N} {b : P.Base} {lam χ : M}
    (hlam : lam ∈ dominantChamber P b) (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) :
    lam + χ ∈ dominantChamber P b :=
  add_mem_dominantChamber P b hlam (mem_dominantChamber_of_forall_coroot'_eq_zero hχ)

namespace LSPath

/-! ### Encoding-level coherence of `centralTransport` and pure-central shapes -/

section EncodingCoherence

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]

/-- **Central transport by `0` is the identity** up to `add_zero` on shapes. -/
theorem centralTransport_zero {lam : M} (h0 : ∀ i ∈ b.support, P.coroot' i (0 : M) = 0)
    (π : LSPath P b lam) :
    centralTransport (0 : M) h0 π = congr (add_zero lam).symm π :=
  eq_of_length_dir_time (by simp) (fun _ ↦ by simp) (fun _ ↦ by simp)

/-- **Successive central transports compose additively** on encodings, up to `add_assoc`. -/
theorem centralTransport_centralTransport {lam χ ψ : M}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hψ : ∀ i ∈ b.support, P.coroot' i ψ = 0)
    (π : LSPath P b lam) :
    centralTransport ψ hψ (centralTransport χ hχ π) =
      congr (add_assoc lam χ ψ).symm
        (centralTransport (χ + ψ) (fun i hi ↦ by rw [map_add, hχ i hi, hψ i hi, add_zero]) π) :=
  eq_of_length_dir_time (by simp) (fun _ ↦ by simp) (fun _ ↦ by simp)

/-- **The inverse of central transport by `χ` is central transport by `-χ`** up to
`add_neg_cancel_right` on shapes. -/
theorem centralTransport_symm_apply {lam χ : M}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (π : LSPath P b (lam + χ)) :
    (centralTransport χ hχ).symm π =
      congr (add_neg_cancel_right lam χ)
        (centralTransport (-χ) (fun i hi ↦ by rw [map_neg, hχ i hi, neg_zero]) π) :=
  eq_of_length_dir_time (by simp) (fun _ ↦ by simp) (fun _ ↦ by simp)

/-- Central transport by `-χ` agrees with the inverse of central transport by `χ` up to
`add_neg_cancel_right` on shapes. -/
theorem centralTransport_neg {lam χ : M}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hneg : ∀ i ∈ b.support, P.coroot' i (-χ) = 0)
    (π : LSPath P b (lam + χ)) :
    centralTransport (-χ) hneg π =
      congr (add_neg_cancel_right lam χ).symm ((centralTransport χ hχ).symm π) := by
  rw [centralTransport_symm_apply hχ π, congr_congr]; simp

/-- Central transport commutes with shape congruence. -/
theorem centralTransport_congr {lam lam' χ : M} (h : lam = lam')
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (π : LSPath P b lam) :
    centralTransport χ hχ (congr h π) =
      congr (congrArg (· + χ) h) (centralTransport χ hχ π) := by subst h; simp

/-- **Uniqueness of the LS path for a pure central shape.** If `χ` is annihilated by every simple
coroot (including `χ = 0`, pure central characters, and arbitrary weights when `ι` is empty), every
Lakshmibai–Seshadri path of shape `χ` equals `straight χ`. -/
theorem eq_straight_of_forall_coroot'_eq_zero {χ : M}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0) (π : LSPath P b χ) :
    π = straight χ := by
  have := P.flip_isReduced
  rw [eq_straight_iff_dir_zero_eq_one]
  exact eq_of_isMinimalCosetRep_of_smul_eq
    (mem_dominantChamber_of_forall_coroot'_eq_zero hχ) (π.dir 0).2
    ((weylCoxeterSystem P b).isMinimalCosetRep_one _)
    (by rw [smul_eq_self_of_forall_coroot'_eq_zero b hχ, one_smul])

end EncodingCoherence

/-! ### Compatibility with `LSPath.crystal` and the twisted central-transport isomorphisms -/

section CrystalTransport

open scoped TensorProduct

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y]
  {P : RootDatum ι X Y} {b : P.Base} [Finite ι] [P.IsReduced] {lam : X}

private abbrev mkRatAddHom (X : Type*) [AddCommGroup X] : X →+ (ℚ ⊗[ℤ] X) :=
  (TensorProduct.mk ℤ ℚ X 1).toAddMonoidHom

/-- Central transport shifts the lattice-valued weight of an LS path by `χ`. -/
theorem weight_centralTransport (hlam : lam ∈ dominantChamber P b) {χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b)
    (π : LSPath P b lam) :
    (centralTransport χ hχ π).weight hlam' = π.weight hlam + χ := by
  apply RootPairing.injective_mk_rat P
  change mkRatAddHom X _ = mkRatAddHom X _
  rw [apply_weight ℚ (mkRatAddHom X) hlam', map_add, apply_weight ℚ (mkRatAddHom X) hlam,
    endpoint_toPLPath_centralTransport]

/-- **Central transport commutes with crystal lowering operators.** -/
theorem crystal_f_centralTransport (hlam : lam ∈ dominantChamber P b) {χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b)
    (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').f i (centralTransport χ hχ π) =
      ((crystal hlam).f i π).map (centralTransport χ hχ) := by
  have := P.flip_isReduced
  let f₀ : X →+ (ℚ ⊗[ℤ] X) := mkRatAddHom X
  let F₀ : Module.Dual ℚ (ℚ ⊗[ℤ] X) := RootPairing.corootRat P i
  have hf₀ : Function.Injective f₀ := RootPairing.injective_mk_rat P
  have hF₀ (x : X) : F₀ (f₀ x) = (P.coroot' i x : ℚ) := RootPairing.corootRat_mk_one P i x
  have hFχ : F₀ (f₀ χ) = 0 := by rw [hF₀ χ, hχ i i.2, Int.cast_zero]
  have hS₀ (μ : X) := RootPairing.pairwise_not_sameRay_mk_rat_orbit P b μ
  apply Option.map_injective (toPLPath_injective (𝕜 := ℚ) (f := f₀) hlam' hf₀.injOn (hS₀ (lam + χ)))
  rw [← lower_toPLPath hlam' f₀ i F₀ hF₀]
  have hlow₀ := lower_toPLPath hlam f₀ i F₀ hF₀ π
  cases hf : (crystal hlam).f i π with
  | none =>
    rw [hf, Option.map_none, toPLPath_def, PLPath.lower_ofSegments_map_snd,
      Option.map_eq_none_iff] at hlow₀
    rw [Option.map_none, Option.map_none, toPLPath_centralTransport_eq_ofSegments,
      PLPath.lower_ofSegments_shiftTimed (π.timed ℚ f₀) hFχ (f₀ (P.root i)), hlow₀, Option.map_none]
  | some ρ =>
    rw [hf, Option.map_some, toPLPath_def] at hlow₀
    have hmaps := P.mapsTo_preReflection_image_orbit_weylGroup i hF₀ lam
    rw [MulAction.orbit, ← Set.range_comp] at hmaps
    obtain ⟨Γ, hΓ, hseg⟩ := PLPath.distinguished_of_lower_eq_some
      (π.isDistinguished_timed ℚ f₀ hlam hf₀.injOn) hmaps (hS₀ lam) hlow₀
    have hΓeq : Γ = PLPath.ofSegments ℚ (ρ.timed ℚ f₀) := by
      rw [← PLPath.ofSegments_segments Γ, ← hseg, toPLPath_def,
        PLPath.distinguished_ofSegments (ρ.isDistinguished_timed ℚ f₀ hlam hf₀.injOn) (hS₀ lam)]
    rw [Option.map_some, Option.map_some, toPLPath_centralTransport_eq_ofSegments,
      PLPath.lower_ofSegments_shiftTimed (π.timed ℚ f₀) hFχ (f₀ (P.root i)), hΓ, Option.map_some,
      hΓeq, PLPath.shiftGraph_ofSegments, PLPath.map_ofSegments, LinearMap.coe_snd,
      ← toPLPath_centralTransport_eq_ofSegments]

/-- **Central transport commutes with crystal raising operators.** -/
theorem crystal_e_centralTransport (hlam : lam ∈ dominantChamber P b) {χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b)
    (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').e i (centralTransport χ hχ π) =
      ((crystal hlam).e i π).map (centralTransport χ hχ) := by
  cases he : (crystal hlam).e i π with
  | some ρ =>
    rw [Option.map_some, (crystal hlam').e_eq_some_iff,
      crystal_f_centralTransport hlam hχ hlam' i ρ, (crystal hlam).e_eq_some_iff.mp he,
      Option.map_some]
  | none =>
    rw [Option.map_none, Option.eq_none_iff_forall_ne_some]
    intro τ hτ
    obtain ⟨ρ, rfl⟩ := (centralTransport χ hχ).surjective τ
    rw [(crystal hlam').e_eq_some_iff, crystal_f_centralTransport hlam hχ hlam' i ρ,
      Option.map_eq_some_iff] at hτ
    obtain ⟨π₀, hπ₀, hπeq⟩ := hτ
    obtain rfl := (centralTransport χ hχ).injective hπeq
    exact Option.some_ne_none _ (((crystal hlam).e_eq_some_iff.mpr hπ₀).symm.trans he)

/-- **Central transport from the weight-twisted LS crystal `B(λ)^χ` onto `B(λ + χ)`** (the `σ = 0`
case of `TauCeti.LSPath.centralTransportIso`). -/
noncomputable def centralTransportIsoZero (hlam : lam ∈ dominantChamber P b) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b :=
      add_mem_dominantChamber_of_forall_coroot'_eq_zero hlam
        fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩)) :
    NormalCrystal.StrictIso ((crystal hlam).weightTwist χ hχ) (crystal hlam') where
  toEquiv := centralTransport χ fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩)
  wt_toFun π := by
    simp only [Equiv.toFun_as_coe, crystal_wt, NormalCrystal.weightTwist_wt]
    rw [weight_centralTransport hlam]
  e_toFun i π := by
    simpa using crystal_e_centralTransport hlam
      (fun j hj ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨j, hj⟩)) hlam' i π

@[simp]
theorem coe_centralTransportIsoZero (hlam : lam ∈ dominantChamber P b) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) :
    ⇑(centralTransportIsoZero hlam χ hχ hlam') =
      centralTransport χ (fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩)) :=
  (rfl)

@[simp]
theorem centralTransportIsoZero_apply (hlam : lam ∈ dominantChamber P b) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) (π : LSPath P b lam) :
    centralTransportIsoZero hlam χ hχ hlam' π =
      centralTransport χ (fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩)) π :=
  (rfl)

theorem crystal_ε_centralTransport (hlam : lam ∈ dominantChamber P b) {χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b)
    (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').ε i (centralTransport χ hχ π) = (crystal hlam).ε i π :=
  ((centralTransportIsoZero hlam χ
    (fun j ↦ (P.toLinearMap.flip_apply _ _).symm.trans (hχ j j.2)) hlam').ε_apply i π).trans
    (by simp)

theorem crystal_φ_centralTransport (hlam : lam ∈ dominantChamber P b) {χ : X}
    (hχ : ∀ i ∈ b.support, P.coroot' i χ = 0)
    (hlam' : lam + χ ∈ dominantChamber P b)
    (i : b.support) (π : LSPath P b lam) :
    (crystal hlam').φ i (centralTransport χ hχ π) = (crystal hlam).φ i π :=
  ((centralTransportIsoZero hlam χ
    (fun j ↦ (P.toLinearMap.flip_apply _ _).symm.trans (hχ j j.2)) hlam').φ_apply i π).trans
    (by simp)

/-- **The two-offset central-transport crystal isomorphism
`T_{λ, χ}^σ : B(λ)^(σ + χ) ≃ B(λ + χ)^σ`.** Its underlying bijection on LS paths is
`LSPath.centralTransport χ _`, independent of the auxiliary central offset `σ`. -/
noncomputable def centralTransportIso (hlam : lam ∈ dominantChamber P b) (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b :=
      add_mem_dominantChamber_of_forall_coroot'_eq_zero hlam
        fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩)) :
    NormalCrystal.StrictIso
      ((crystal hlam).weightTwist (σ + χ) (by simp [map_add, hσ, hχ]))
      ((crystal hlam').weightTwist σ hσ) where
  toEquiv := centralTransport χ fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩)
  wt_toFun π := by
    simp only [Equiv.toFun_as_coe, NormalCrystal.weightTwist_wt, crystal_wt]
    rw [weight_centralTransport hlam]; abel
  e_toFun i π := by
    simpa using crystal_e_centralTransport hlam
      (fun j hj ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨j, hj⟩)) hlam' i π

/-- The underlying path map of `centralTransportIso` is `centralTransport χ _`, independent of the
auxiliary central offset `σ`. -/
@[simp]
theorem coe_centralTransportIso (hlam : lam ∈ dominantChamber P b) (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) :
    ⇑(centralTransportIso hlam χ σ hχ hσ hlam') =
      centralTransport χ (fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩)) :=
  (rfl)

@[simp]
theorem centralTransportIso_apply (hlam : lam ∈ dominantChamber P b) (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) (π : LSPath P b lam) :
    centralTransportIso hlam χ σ hχ hσ hlam' π =
      centralTransport χ (fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩)) π :=
  (rfl)

/-- Specializing `centralTransportIso` to `σ = 0` recovers `centralTransportIsoZero`. -/
theorem centralTransportIso_zero_offset (hlam : lam ∈ dominantChamber P b) (χ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hlam' : lam + χ ∈ dominantChamber P b) :
    ((centralTransportIso hlam χ 0 hχ (by simp) hlam').congrLeft
      (NormalCrystal.weightTwist_congr _ (zero_add χ) _ hχ)).congrRight
      (NormalCrystal.weightTwist_zero (crystal hlam')) =
      centralTransportIsoZero hlam χ hχ hlam' :=
  NormalCrystal.StrictIso.ext fun _ ↦ rfl

/-- **Strict-map identity law `T_{λ, 0}^σ = id`** on `B(λ)^σ`. -/
theorem centralTransportIso_zero (hlam : lam ∈ dominantChamber P b) (σ : X)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlam0 : lam + 0 ∈ dominantChamber P b :=
      add_mem_dominantChamber_of_forall_coroot'_eq_zero hlam fun _ _ ↦ map_zero _) :
    ((centralTransportIso hlam 0 σ (by simp) hσ hlam0).congrLeft
      (NormalCrystal.weightTwist_congr _ (add_zero σ) _ hσ)).trans
      ((congrIso (add_zero lam) hlam0).weightTwist σ hσ) =
      NormalCrystal.StrictIso.refl ((crystal hlam).weightTwist σ hσ) :=
  NormalCrystal.StrictIso.ext fun π ↦ by
    simp only [NormalCrystal.StrictIso.trans_apply, NormalCrystal.StrictIso.coe_congrLeft,
      centralTransportIso_apply, NormalCrystal.StrictIso.coe_weightTwist, coe_congrIso,
      NormalCrystal.StrictIso.refl_apply]
    rw [centralTransport_zero]; simp

/-- **Additive composition law `T_{λ + χ, ψ}^σ ∘ T_{λ, χ}^(σ + ψ) = T_{λ, χ + ψ}^σ`** for central
transports as strict crystal isomorphisms. -/
theorem centralTransportIso_trans_centralTransportIso (hlam : lam ∈ dominantChamber P b)
    (χ ψ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hψ : ∀ i : b.support, P.toLinearMap ψ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlamχ : lam + χ ∈ dominantChamber P b :=
      add_mem_dominantChamber_of_forall_coroot'_eq_zero hlam
        fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩))
    (hlamχψ : (lam + χ) + ψ ∈ dominantChamber P b :=
      add_mem_dominantChamber_of_forall_coroot'_eq_zero
        (add_mem_dominantChamber_of_forall_coroot'_eq_zero hlam
          fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩))
        fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hψ ⟨i, hi⟩))
    (hlam_χψ : lam + (χ + ψ) ∈ dominantChamber P b :=
      add_mem_dominantChamber_of_forall_coroot'_eq_zero hlam
        fun i hi ↦ by simp [RootPairing.coroot', map_add, hχ ⟨i, hi⟩, hψ ⟨i, hi⟩]) :
    ((centralTransportIso hlam χ (σ + ψ) hχ (by simp [map_add, hσ, hψ]) hlamχ).trans
      (centralTransportIso hlamχ ψ σ hψ hσ hlamχψ)).congrLeft
      (NormalCrystal.weightTwist_congr _ (by abel : (σ + ψ) + χ = σ + (χ + ψ)) _
        (by simp [map_add, hσ, hχ, hψ])) =
      (centralTransportIso hlam (χ + ψ) σ (by simp [map_add, hχ, hψ]) hσ hlam_χψ).trans
        ((congrIso (add_assoc lam χ ψ).symm hlam_χψ).weightTwist σ hσ) :=
  NormalCrystal.StrictIso.ext fun π ↦ by simpa using centralTransport_centralTransport _ _ π

/-- **Inverse formula `(T_{λ, χ}^σ)⁻¹ = T_{λ + χ, -χ}^(σ + χ)`** for central transports as strict
crystal isomorphisms. -/
theorem centralTransportIso_symm (hlam : lam ∈ dominantChamber P b) (χ σ : X)
    (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hσ : ∀ i : b.support, P.toLinearMap σ (P.coroot i) = 0)
    (hlamχ : lam + χ ∈ dominantChamber P b :=
      add_mem_dominantChamber_of_forall_coroot'_eq_zero hlam
        fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩))
    (hlamχ_neg : (lam + χ) + (-χ) ∈ dominantChamber P b :=
      add_mem_dominantChamber_of_forall_coroot'_eq_zero
        (add_mem_dominantChamber_of_forall_coroot'_eq_zero hlam
          fun i hi ↦ (P.toLinearMap.flip_apply _ _).trans (hχ ⟨i, hi⟩))
        fun i hi ↦ by simp [RootPairing.coroot', hχ ⟨i, hi⟩]) :
    (centralTransportIso hlam χ σ hχ hσ hlamχ).symm =
      ((centralTransportIso hlamχ (-χ) (σ + χ) (by simp [hχ])
        (by simp [map_add, hσ, hχ]) hlamχ_neg).congrLeft
        (NormalCrystal.weightTwist_congr _ (add_neg_cancel_right σ χ) _ hσ)).trans
        ((congrIso (add_neg_cancel_right lam χ) hlamχ_neg).weightTwist
          (σ + χ) (by simp [map_add, hσ, hχ])) :=
  NormalCrystal.StrictIso.ext fun π ↦ by
    conv_rhs => simp
    rw [← NormalCrystal.StrictIso.coe_toEquiv_symm]
    exact centralTransport_symm_apply _ π

/-! ### Pure-central and zero-shape LS crystals -/

/-- **For any pure central weight `χ` (including `0` and any weight over an empty root system),
`crystal` is strictly isomorphic to the one-element crystal `NormalCrystal.central χ hχ`.** -/
noncomputable def centralIso (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hχ_dom : χ ∈ dominantChamber P b :=
      mem_dominantChamber_of_forall_coroot'_eq_zero fun i hi ↦ hχ ⟨i, hi⟩) :
    NormalCrystal.StrictIso (crystal hχ_dom) (NormalCrystal.central χ hχ) where
  toEquiv :=
    { toFun _ := PUnit.unit
      invFun _ := straight χ
      left_inv π := (eq_straight_of_forall_coroot'_eq_zero (fun i hi ↦ hχ ⟨i, hi⟩) π).symm
      right_inv u := by cases u; rfl }
  wt_toFun π := by rw [eq_straight_of_forall_coroot'_eq_zero (fun i hi ↦ hχ ⟨i, hi⟩) π]; simp
  e_toFun i π := by rw [eq_straight_of_forall_coroot'_eq_zero (fun i hi ↦ hχ ⟨i, hi⟩) π]; simp

@[simp]
theorem centralIso_symm_unit (χ : X) (hχ : ∀ i : b.support, P.toLinearMap χ (P.coroot i) = 0)
    (hχ_dom : χ ∈ dominantChamber P b) :
    (centralIso χ hχ hχ_dom).symm PUnit.unit = straight χ := by
  rw [← NormalCrystal.StrictIso.coe_toEquiv_symm]
  rfl

/-- **The LS path crystal of shape `0` is strictly isomorphic to `NormalCrystal.central 0 _`.** -/
noncomputable def zeroIso :
    NormalCrystal.StrictIso (crystal (zero_mem_dominantChamber P b))
      (NormalCrystal.central (0 : X) (by simp)) :=
  centralIso 0 (by simp) (zero_mem_dominantChamber P b)

end CrystalTransport

end LSPath

end TauCeti

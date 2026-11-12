/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import TauCeti.RingTheory.Huber.Pair.Complete
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Plus
import TauCeti.RingTheory.Ideal.Quotient.Frobenius
import TauCeti.RingTheory.WittVector.TeichmullerCoeff

/-!
# Fontaine's map for the tilt of a complete uniform Tate ring

Let `B` be a nonzero complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent,
with tilt `B♭ = uniformTilt p B`, and let `B⁺ ⊆ B°` be a ring of integral elements, with integral
tilt `B♭⁺ = lim_{x ↦ x ^ p} B⁺`. Then `p` is not a unit of `B⁺` and `B⁺` is `p`-adically complete,
so Mathlib's tilt `PreTilt B⁺ p = lim_{x ↦ x ^ p} B⁺ ⧸ p` and Fontaine's map
`WittVector.fontaineTheta B⁺ p : W(PreTilt B⁺ p) → B⁺` are defined. Reducing every coordinate
modulo `p` identifies `B♭⁺` with `PreTilt B⁺ p` as rings, and under this identification the sharp
map `x ↦ x♯ = x⁽⁰⁾` of `B♭⁺` is Mathlib's `PreTilt.untilt`. Transporting `fontaineTheta` along it
gives *Fontaine's map* `θ_B : W(B♭⁺) → B⁺`, `∑ₙ [xₙ] pⁿ ↦ ∑ₙ xₙ♯ pⁿ`.

The map `θ_B` is the unique ring homomorphism `W(B♭⁺) → B⁺` sending each Teichmüller
representative `[x]` to `x♯`, it is natural in `B` for continuous plus-preserving ring
homomorphisms, and it is surjective when Frobenius is surjective on `B⁺ ⧸ p`, for instance when `B`
is perfectoid. Perfectoidness is not assumed anywhere else.

## Main definitions

* `TauCeti.Perfectoid.uniformTilt.plusEquivPreTilt p h`: the ring isomorphism
  `B♭⁺ ≃+* PreTilt B⁺ p`, `x ↦ (x⁽ⁿ⁾ mod p)ₙ`.
* `TauCeti.Perfectoid.uniformTilt.theta p h`: Fontaine's map `θ_B : W(B♭⁺) →+* B⁺`.

## Main results

* `TauCeti.Perfectoid.uniformTilt.untilt_plusEquivPreTilt`: `PreTilt.untilt` corresponds to the
  sharp map of `B♭⁺`.
* `TauCeti.Perfectoid.uniformTilt.theta_eq_fontaineTheta`: `θ_B` is Mathlib's `fontaineTheta`
  under `B♭⁺ ≃+* PreTilt B⁺ p`.
* `TauCeti.Perfectoid.uniformTilt.theta_teichmuller`: `θ_B [x] = x♯`.
* `TauCeti.Perfectoid.uniformTilt.theta_unique`: `θ_B` is the only ring homomorphism with this
  property.
* `TauCeti.Perfectoid.uniformTilt.theta_map`: naturality, `θ_C ∘ W(g♭) = g ∘ θ_B`.
* `TauCeti.Perfectoid.uniformTilt.surjective_theta`: `θ_B` is surjective when Frobenius is
  surjective modulo `p`.

## References

* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, Lemma 2.7.1 and
  Definition 2.7.3.
* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Lemma 3.2 and Definition 3.5.
-/

public section

open TauCeti.Huber
open WittVector (teichmuller)

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} {B : Type*} [CommRing B] [Fact p.Prime] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [hpn : Fact (IsTopologicallyNilpotent (p : B))]
  {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)

local notation "𝕎" => WittVector p

section PreTilt

variable [Fact (¬IsUnit (p : Bplus))]

variable (p) in
/-- **The integral tilt is Mathlib's `PreTilt`**: reducing every coordinate modulo `p` is a ring
isomorphism `B♭⁺ ≃+* PreTilt B⁺ p = lim_{x ↦ x ^ p} B⁺ ⧸ p`. This is `plusEquiv` for the ideal
`(p)`, with Mathlib's `PreTilt` as target. -/
noncomputable def plusEquivPreTilt : plusSubring p h ≃+* PreTilt Bplus p :=
  have := h.isAdicComplete_span_natCast p hpn.out
  plusEquiv h (Ideal.span {(p : Bplus)})

/-- `plusEquivPreTilt` is `plusEquiv` for the ideal `(p)`; this holds by definition, as
`PreTilt B⁺ p` is defined to be `Perfection (B⁺ ⧸ p) p`. -/
theorem plusEquivPreTilt_apply [IsAdicComplete (Ideal.span {(p : Bplus)}) Bplus]
    (x : plusSubring p h) : plusEquivPreTilt p h x = plusEquiv h (Ideal.span {(p : Bplus)}) x :=
  (rfl)

/-- The inverse of `plusEquivPreTilt` is the inverse of `plusEquiv` for the ideal `(p)`. -/
theorem plusEquivPreTilt_symm_apply [IsAdicComplete (Ideal.span {(p : Bplus)}) Bplus]
    (y : PreTilt Bplus p) :
    (plusEquivPreTilt p h).symm y = (plusEquiv h (Ideal.span {(p : Bplus)})).symm y :=
  (rfl)

/-- `plusEquivPreTilt` reduces every coordinate modulo `p`. -/
@[simp]
theorem coeff_plusEquivPreTilt (x : plusSubring p h) (n : ℕ) :
    PreTilt.coeff n (plusEquivPreTilt p h x) =
      Ideal.Quotient.mk _ ⟨coeff p B n x, mem_plusSubring_iff.mp x.2 n⟩ := by
  have := h.isAdicComplete_span_natCast p hpn.out
  rw [PreTilt.coeff_def, plusEquivPreTilt_apply, coeff_plusEquiv]

variable [IsAdicComplete (Ideal.span {(p : Bplus)}) Bplus]

/-- The sharp map of the inverse of `plusEquivPreTilt` is Mathlib's `PreTilt.untilt`. -/
@[simp]
theorem plusSharp_plusEquivPreTilt_symm (y : PreTilt Bplus p) :
    plusSharp p h ((plusEquivPreTilt p h).symm y) = PreTilt.untilt y :=
  Subtype.ext <| by
    rw [coe_plusSharp, plusEquivPreTilt_symm_apply]
    refine (coeff_zero_plusEquiv_symm h _ y).trans ?_
    -- `PreTilt.untilt` is the Teichmüller map of `PreTilt B⁺ p = Perfection (B⁺ ⧸ p) p`
    unfold PreTilt.untilt
    exact congrArg Subtype.val (congrFun Perfection.coe_teichmuller_eq_teichmuller₀ y).symm

/-- **The sharp map is `PreTilt.untilt`**: under `B♭⁺ ≃+* PreTilt B⁺ p`, Mathlib's untilt
`PreTilt B⁺ p → B⁺` is the sharp map `x ↦ x♯ = x⁽⁰⁾`. -/
@[simp]
theorem untilt_plusEquivPreTilt (x : plusSubring p h) :
    PreTilt.untilt (plusEquivPreTilt p h x) = plusSharp p h x := by
  rw [← plusSharp_plusEquivPreTilt_symm h, RingEquiv.symm_apply_apply]

end PreTilt

/-- Ring homomorphisms from `W(B♭⁺)` to a `p`-adically separated ring agree once they agree on
Teichmüller representatives, as `B♭⁺ ≃+* PreTilt B⁺ p` is perfect of characteristic `p`. -/
private theorem ringHom_ext_teichmuller [Nontrivial B] {S : Type*} [CommRing S]
    [IsHausdorff (Ideal.span {(p : S)}) S] {f g : 𝕎 (plusSubring p h) →+* S}
    (hfg : ∀ x, f (teichmuller p x) = g (teichmuller p x)) : f = g := by
  have : Fact (¬IsUnit (p : Bplus)) :=
    ⟨h.not_isUnit_natCast_of_isTopologicallyNilpotent p hpn.out⟩
  let e := plusEquivPreTilt p h
  -- compare `f` and `g` on `W(PreTilt B⁺ p)`, where the Teichmüller expansion applies
  have he : f.comp (WittVector.map e.symm.toRingHom) = g.comp (WittVector.map e.symm.toRingHom) :=
    WittVector.ringHom_ext_teichmuller fun y ↦ by simpa using hfg (e.symm y)
  ext x
  have hx : WittVector.map e.symm.toRingHom (WittVector.map e.toRingHom x) = x :=
    WittVector.ext fun n ↦ by simp
  have hfg' := RingHom.congr_fun he (WittVector.map e.toRingHom x)
  rwa [RingHom.comp_apply, RingHom.comp_apply, hx] at hfg'

section Theta

variable [Nontrivial B]

variable (p) in
/-- **Fontaine's map** `θ_B : W(B♭⁺) → B⁺` of the tilt of a nonzero complete uniform Tate ring in
which `p` is topologically nilpotent, `∑ₙ [xₙ] pⁿ ↦ ∑ₙ xₙ♯ pⁿ`. It is Mathlib's
`WittVector.fontaineTheta` transported along `B♭⁺ ≃+* PreTilt B⁺ p`
(`theta_eq_fontaineTheta`), and it is characterised by `θ_B [x] = x♯` (`theta_teichmuller`,
`theta_unique`). -/
noncomputable def theta : 𝕎 (plusSubring p h) →+* Bplus :=
  have : Fact (¬IsUnit (p : Bplus)) :=
    ⟨h.not_isUnit_natCast_of_isTopologicallyNilpotent p hpn.out⟩
  have := h.isAdicComplete_span_natCast p hpn.out
  (WittVector.fontaineTheta Bplus p).comp (WittVector.map (plusEquivPreTilt p h).toRingHom)

/-- `θ_B` is Mathlib's `fontaineTheta` under the identification `B♭⁺ ≃+* PreTilt B⁺ p`. -/
theorem theta_eq_fontaineTheta [Fact (¬IsUnit (p : Bplus))]
    [IsAdicComplete (Ideal.span {(p : Bplus)}) Bplus] :
    theta p h = (WittVector.fontaineTheta Bplus p).comp
      (WittVector.map (plusEquivPreTilt p h).toRingHom) :=
  (rfl)

/-- **`θ_B [x] = x♯`**: Fontaine's map sends the Teichmüller representative of `x ∈ B♭⁺` to its
sharp. -/
@[simp]
theorem theta_teichmuller (x : plusSubring p h) :
    theta p h (teichmuller p x) = plusSharp p h x := by
  have : Fact (¬IsUnit (p : Bplus)) :=
    ⟨h.not_isUnit_natCast_of_isTopologicallyNilpotent p hpn.out⟩
  have := h.isAdicComplete_span_natCast p hpn.out
  simp [theta_eq_fontaineTheta, WittVector.map_teichmuller, WittVector.fontaineTheta_teichmuller]

/-- **Uniqueness of Fontaine's map**: `θ_B` is the only ring homomorphism `W(B♭⁺) → B⁺` sending
the Teichmüller representative `[x]` to `x♯` for every `x ∈ B♭⁺`. -/
theorem theta_unique (f : 𝕎 (plusSubring p h) →+* Bplus)
    (hf : ∀ x, f (teichmuller p x) = plusSharp p h x) : f = theta p h :=
  have := h.isAdicComplete_span_natCast p hpn.out
  ringHom_ext_teichmuller h fun x ↦ by rw [hf, theta_teichmuller]

/-- Fontaine's map is surjective when every element of `B⁺` is a `p`-th power modulo `p`, that is,
when Frobenius is surjective on `B⁺ ⧸ p`; this holds when `B` is perfectoid. -/
theorem surjective_theta (hF : ∀ x : Bplus, ∃ y, (p : Bplus) ∣ x - y ^ p) :
    Function.Surjective (theta p h) := by
  have : Fact (¬IsUnit (p : Bplus)) :=
    ⟨h.not_isUnit_natCast_of_isTopologicallyNilpotent p hpn.out⟩
  have := h.isAdicComplete_span_natCast p hpn.out
  rw [theta_eq_fontaineTheta, RingHom.coe_comp]
  exact (surjective_fontaineTheta ((surjective_frobenius_modP_iff (p := p) Bplus).mpr hF)).comp
    (WittVector.map_surjective _ (plusEquivPreTilt p h).surjective)

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [IsTateRing C] [CompleteSpace C] [T2Space C] [IsUniform C]
  [Fact (IsTopologicallyNilpotent (p : C))] [Nontrivial C]
  {Cplus : Subring C} (hC : IsRingOfIntegralElements Cplus)
  (g : B →+* C) (hg : Continuous g) (hgplus : ∀ x ∈ Bplus, g x ∈ Cplus)

/-- **Naturality of Fontaine's map**: for a continuous ring homomorphism `g : B → C` carrying `B⁺`
into `C⁺`, `θ_C ∘ W(g♭) = g ∘ θ_B` on `W(B♭⁺)`. -/
theorem theta_map (x : 𝕎 (plusSubring p h)) :
    (theta p hC (WittVector.map ((map (p := p) g hg).restrict _ _
      fun _ hy ↦ map_mem_plusSubring g hg hgplus hy) x) : C) = g (theta p h x) := by
  have := hC.isAdicComplete_span_natCast p Fact.out
  have hext : (theta p hC).comp (WittVector.map ((map (p := p) g hg).restrict _ _
      fun _ hy ↦ map_mem_plusSubring g hg hgplus hy)) =
      (g.restrict Bplus Cplus hgplus).comp (theta p h) :=
    ringHom_ext_teichmuller h fun y ↦ Subtype.ext <| by simp [WittVector.map_teichmuller]
  simpa using congrArg Subtype.val (RingHom.congr_fun hext x)

end Theta

end TauCeti.Perfectoid.uniformTilt

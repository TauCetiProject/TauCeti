/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Subring
public import Mathlib.RingTheory.Perfectoid.FontaineTheta
public import TauCeti.RingTheory.Huber.Pair.Complete
public import TauCeti.RingTheory.Perfectoid.UniformTilt.Plus
public import TauCeti.RingTheory.WittVector.TeichmullerCoeff

/-!
# The integral tilt is `PreTilt`, and Fontaine's map on it

Let `B` be a nonzero complete Hausdorff uniform Tate ring in which `p` is topologically nilpotent,
and let `B⁺ ⊆ B°` be a ring of integral elements. Then `B⁺` is `p`-adically complete and `p` is not
a unit of `B⁺`, the standing hypotheses of Mathlib's `PreTilt.untilt` and
`WittVector.fontaineTheta`. No perfectoid hypothesis is needed for this, and `p` need not be a
unit, a nonzerodivisor or even nonzero in `B`.

The integral tilt `B♭⁺ = lim_{x ↦ x ^ p} B⁺` is then Mathlib's `PreTilt B⁺ p`: reducing every
coordinate modulo `p` is a ring isomorphism, which identifies the zeroth coordinate
`x ↦ x⁽⁰⁾ = x♯` of `B♭⁺` with `PreTilt.untilt`. The sharp map is multiplicative and not additive,
but it extends to Fontaine's ring homomorphism `θ : W(B♭⁺) → B⁺`, the unique ring homomorphism with
`θ [x] = x♯`. This is Mathlib's `WittVector.fontaineTheta` transported along the comparison, it is
natural in `B`, and modulo `p` it is `x ↦ (x₀)♯`, where `x₀` is the zeroth Witt coordinate. In
characteristic `p` it is the map `x ↦ (x₀)♯` itself.

The zero ring is excluded: there `p` is a unit of `B⁺ = 0`, so that Mathlib's constructions do not
apply, and the only map to `B⁺` is the zero map.

## Main definitions

* `TauCeti.Perfectoid.uniformTilt.plusEquivPreTilt h`: the ring isomorphism
  `B♭⁺ ≃+* PreTilt B⁺ p`.
* `TauCeti.Perfectoid.uniformTilt.theta h`: Fontaine's map `θ : W(B♭⁺) →+* B⁺`.

## Main results

* `TauCeti.Perfectoid.uniformTilt.coe_untilt_plusEquivPreTilt`: `PreTilt.untilt` is the zeroth
  coordinate of `B♭⁺`.
* `TauCeti.Perfectoid.uniformTilt.coe_theta_teichmuller`: `θ [x] = x♯`.
* `TauCeti.Perfectoid.uniformTilt.theta_unique`: these values determine `θ`.
* `TauCeti.Perfectoid.uniformTilt.theta_eq_fontaineTheta`: `θ` is `WittVector.fontaineTheta`.
* `TauCeti.Perfectoid.uniformTilt.theta_natural`: `θ_C ∘ W(g♭) = g ∘ θ_B`.
* `TauCeti.Perfectoid.uniformTilt.mk_theta`: the reduction of `θ` modulo `p`.
* `TauCeti.Perfectoid.uniformTilt.coe_theta_of_charP`: the form of `θ` in characteristic `p`.

## References

* K. S. Kedlaya, *Nonarchimedean geometry of Witt vectors and the tilting equivalence*, in
  *Perfectoid Spaces: Lectures from the 2017 Arizona Winter School*, Lemma 2.7.1 and Definition
  2.7.3.
* P. Scholze, *Étale cohomology of diamonds*, Lemma 3.14(i).
* B. Bhatt, M. Morrow, P. Scholze, *Integral p-adic Hodge theory*, Lemma 3.2 and Definition 3.5.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid.uniformTilt

variable {p : ℕ} {B : Type*} [CommRing B] [hp : Fact p.Prime] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [hpn : Fact (IsTopologicallyNilpotent (p : B))]

variable {Bplus : Subring B} (h : IsRingOfIntegralElements Bplus)

section PreTilt

variable [Fact ¬IsUnit (p : Bplus)] [IsAdicComplete (Ideal.span {(p : Bplus)}) Bplus]

/-- **The integral tilt is Mathlib's `PreTilt`**: reducing every coordinate modulo `p` is a ring
isomorphism `B♭⁺ ≃+* PreTilt B⁺ p`. The instance hypotheses are those of `PreTilt.untilt`; they
hold for nonzero `B` by `IsRingOfIntegralElements.not_isUnit_natCast` and
`IsRingOfIntegralElements.isAdicComplete_span_natCast`. -/
noncomputable def plusEquivPreTilt : plusSubring p h ≃+* PreTilt Bplus p :=
  plusEquiv h (Ideal.span {(p : Bplus)})

/-- `plusEquivPreTilt` reduces every coordinate modulo `p`. -/
@[simp]
theorem coeff_plusEquivPreTilt (x : plusSubring p h) (n : ℕ) :
    PreTilt.coeff n (plusEquivPreTilt h x) =
      Ideal.Quotient.mk _ ⟨coeff p B n x, mem_plusSubring_iff.mp x.2 n⟩ :=
  coeff_plusEquiv h _ x n

/-- Under `plusEquivPreTilt`, `PreTilt.untilt` is the zeroth coordinate `x ↦ x♯` of `B♭⁺`. -/
@[simp]
theorem coe_untilt_plusEquivPreTilt (x : plusSubring p h) :
    ((PreTilt.untilt (plusEquivPreTilt h x) : Bplus) : B) = coeff p B 0 x := by
  have hx := coeff_zero_plusEquiv_symm h (Ideal.span {(p : Bplus)})
    (plusEquiv h (Ideal.span {(p : Bplus)}) x)
  rw [RingEquiv.symm_apply_apply] at hx
  -- `PreTilt.untilt` is by definition `Perfection.teichmuller₀` for the ideal `(p)`
  exact hx.symm

/-- The zeroth coordinate of the inverse of `plusEquivPreTilt` is `PreTilt.untilt`. -/
@[simp]
theorem coeff_zero_plusEquivPreTilt_symm (y : PreTilt Bplus p) :
    coeff p B 0 ((plusEquivPreTilt h).symm y : uniformTilt p B) = (PreTilt.untilt y : Bplus) := by
  rw [← coe_untilt_plusEquivPreTilt, RingEquiv.apply_symm_apply]

end PreTilt

section Theta

variable [Nontrivial B]

/-- **Fontaine's map** `θ : W(B♭⁺) → B⁺`: the unique ring homomorphism with `θ [x] = x♯`
(`coe_theta_teichmuller`, `theta_unique`). It is Mathlib's `WittVector.fontaineTheta` transported
along `plusEquivPreTilt` (`theta_eq_fontaineTheta`). -/
noncomputable def theta : WittVector p (plusSubring p h) →+* Bplus :=
  haveI : Fact ¬IsUnit (p : Bplus) := ⟨h.not_isUnit_natCast⟩
  haveI := h.isAdicComplete_span_natCast (p := p)
  (WittVector.fontaineTheta Bplus p).comp (WittVector.map (plusEquivPreTilt h).toRingHom)

/-- `θ` is Mathlib's `WittVector.fontaineTheta` under `B♭⁺ ≃+* PreTilt B⁺ p`. -/
theorem theta_eq_fontaineTheta [Fact ¬IsUnit (p : Bplus)]
    [IsAdicComplete (Ideal.span {(p : Bplus)}) Bplus] :
    theta h = (WittVector.fontaineTheta Bplus p).comp
      (WittVector.map (plusEquivPreTilt h).toRingHom) := (rfl)

/-- `θ` sends the Teichmüller representative of `x` to `x♯`. -/
@[simp]
theorem coe_theta_teichmuller (x : plusSubring p h) :
    (theta h (WittVector.teichmuller p x) : B) = coeff p B 0 x := by
  have : Fact ¬IsUnit (p : Bplus) := ⟨h.not_isUnit_natCast⟩
  have := h.isAdicComplete_span_natCast (p := p)
  simp [theta_eq_fontaineTheta, WittVector.map_teichmuller]

/-- `θ` is the only ring homomorphism `W(B♭⁺) → B⁺` sending `[x]` to `x♯`. -/
theorem theta_unique (f : WittVector p (plusSubring p h) →+* Bplus)
    (hf : ∀ x, (f (WittVector.teichmuller p x) : B) = coeff p B 0 x) : f = theta h := by
  have := h.isAdicComplete_span_natCast (p := p)
  exact WittVector.eq_of_apply_teichmuller_eq_of_isHausdorff fun x ↦
    Subtype.ext <| by rw [hf, coe_theta_teichmuller]

/-- `θ` modulo `p` is the sharp of the zeroth Witt coordinate, modulo `p`. -/
theorem mk_theta (x : WittVector p (plusSubring p h)) :
    Ideal.Quotient.mk (Ideal.span {(p : Bplus)}) (theta h x) =
      Ideal.Quotient.mk _ ⟨coeff p B 0 (x.coeff 0), mem_plusSubring_iff.mp (x.coeff 0).2 0⟩ := by
  have : Fact ¬IsUnit (p : Bplus) := ⟨h.not_isUnit_natCast⟩
  have := h.isAdicComplete_span_natCast (p := p)
  simp [theta_eq_fontaineTheta, WittVector.mk_fontaineTheta]

/-- In characteristic `p`, `θ` is the sharp of the zeroth Witt coordinate. -/
theorem coe_theta_of_charP [CharP B p] (x : WittVector p (plusSubring p h)) :
    (theta h x : B) = coeff p B 0 (x.coeff 0) := by
  have hp0 : (p : Bplus) = 0 := Subtype.ext (by simp)
  have hx := Ideal.Quotient.eq.mp (mk_theta h x)
  rw [hp0, Ideal.span_singleton_zero, Ideal.mem_bot, sub_eq_zero] at hx
  exact congrArg Subtype.val hx

variable {C : Type*} [CommRing C] [UniformSpace C] [IsUniformAddGroup C] [IsTopologicalRing C]
  [IsTateRing C] [CompleteSpace C] [T2Space C] [IsUniform C]
  [Fact (IsTopologicallyNilpotent (p : C))] [Nontrivial C] {Cplus : Subring C}

/-- **Naturality of `θ`**: for a continuous ring homomorphism `g : B → C` carrying `B⁺` into `C⁺`,
`θ_C ∘ W(g♭) = g ∘ θ_B`. -/
theorem theta_natural (hC : IsRingOfIntegralElements Cplus) (g : B →+* C) (hg : Continuous g)
    (hgp : ∀ x ∈ Bplus, g x ∈ Cplus) :
    (theta hC).comp (WittVector.map (plusMap (p := p) h hC g hg hgp)) =
      (g.restrict Bplus Cplus hgp).comp (theta h) := by
  have := hC.isAdicComplete_span_natCast (p := p)
  refine WittVector.eq_of_apply_teichmuller_eq_of_isHausdorff fun x ↦ Subtype.ext ?_
  simp [WittVector.map_teichmuller]

end Theta

end TauCeti.Perfectoid.uniformTilt

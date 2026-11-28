/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Localization.FractionRing
public import TauCeti.RingTheory.Perfectoid.PreTilt.Map
public import TauCeti.RingTheory.WittVector.Action

/-!
# Group actions on tilts and on Fontaine's map

Let a monoid `G` act on a commutative ring `A` by ring endomorphisms, and let `p` be a prime that is
not a unit of `A`. By functoriality of the tilt (`PreTilt.map`), `G` acts on the tilt
`A♭ = PreTilt A p` by ring endomorphisms, `g` acting by `PreTilt.map p g`, that is on every
coordinate of a compatible system of `p`-th roots in `A ⧸ p`. Then `G` acts on the Witt vectors
`W(A♭)` (`WittVector.mulSemiringAction`), and when `G` is a group and `A♭` a domain (for instance
when `A` is a `p`-adically complete domain), on the fraction field `Frac(A♭)` and on
`W(Frac(A♭))`, compatibly with `W(A♭) → W(Frac(A♭))`. In the main example the absolute Galois
group `Gal(PadicAlgCl p / ℚ_p)` of `ℚ_p` acts on the valuation ring `A = O_C` of `C = ℂ_p`, and
these are its actions on `O_C♭`, on `C♭ = Frac(O_C♭)`, on `A_inf = W(O_C♭)` and on `W(C♭)`.

By naturality, when `A` is `p`-adically complete the sharp map `x ↦ x♯` and Fontaine's map
`θ : W(A♭) → A` are `G`-equivariant, and the action commutes with the inverse of the Frobenius of
the perfect ring `A♭`.

## Main definitions

* `PreTilt.instMulSemiringAction`: the action of `G` on `A♭`.
* `PreTilt.instMulSemiringActionFractionRing`: for a group `G` and a domain `A♭`, the action of
  `G` on `Frac(A♭)`.

## Main results

* `PreTilt.coeff_smul`: `G` acts on the coordinates of `A♭` through the reduction modulo `p` of its
  action on `A`.
* `PreTilt.iterate_frobeniusEquiv_symm_smul`: the action commutes with the `p ^ n`-th root maps
  of `A♭`.
* `PreTilt.untilt_smul`: the sharp map is equivariant, `(g • x)♯ = g • x♯`.
* `WittVector.fontaineTheta_smul`: Fontaine's map is equivariant, `θ (g • w) = g • θ w`.
* `PreTilt.smul_algebraMap_fractionRing`, `PreTilt.map_algebraMap_fractionRing_smul`: the
  inclusions `A♭ → Frac(A♭)` and `W(A♭) → W(Frac(A♭))` are equivariant.

## References

* B. Bhatt, M. Morrow, P. Scholze, *Integral `p`-adic Hodge theory*, §3.
* J.-M. Fontaine, *Le corps des périodes `p`-adiques*, Astérisque 223 (1994).
-/

public section

namespace PreTilt

variable {G A : Type*} [Monoid G] [CommRing A] [MulSemiringAction G A] {p : ℕ} [Fact p.Prime]
  [Fact ¬IsUnit (p : A)]

/-- A monoid acting on `A` by ring endomorphisms acts on the tilt `A♭ = PreTilt A p` by ring
endomorphisms: `g` acts by the map of tilts `PreTilt.map p g` induced by `g`. -/
noncomputable instance instMulSemiringAction : MulSemiringAction G (PreTilt A p) :=
  MulSemiringAction.compHom (PreTilt A p)
    ({ toFun g := map p (MulSemiringAction.toRingHom G A g)
       map_one' := by
         rw [show MulSemiringAction.toRingHom G A 1 = RingHom.id A from RingHom.ext (one_smul G),
           map_id]
         rfl
       map_mul' g h := by
         rw [show MulSemiringAction.toRingHom G A (g * h) = (MulSemiringAction.toRingHom G A g).comp
           (MulSemiringAction.toRingHom G A h) from RingHom.ext (mul_smul g h), map_comp]
         rfl } :
      G →* (PreTilt A p →+* PreTilt A p))

theorem smul_def (g : G) (x : PreTilt A p) :
    g • x = map p (MulSemiringAction.toRingHom G A g) x :=
  (rfl)

/-- The ring endomorphism of `A♭` by which `g` acts is the map of tilts induced by `g`. -/
theorem toRingHom_eq_map (g : G) :
    MulSemiringAction.toRingHom G (PreTilt A p) g = map p (MulSemiringAction.toRingHom G A g) :=
  RingHom.ext fun _ ↦ (rfl)

/-- `G` acts on the coordinates of `A♭` by the reduction modulo `p` of its action on `A`. -/
@[simp]
theorem coeff_smul (g : G) (x : PreTilt A p) (n : ℕ) :
    coeff n (g • x) = ModP.map p (MulSemiringAction.toRingHom G A g) (coeff n x) :=
  coeff_map _ x n

/-- The action of `G` commutes with the `p`-th root map of the perfect ring `A♭`. -/
@[simp]
theorem frobeniusEquiv_symm_smul (g : G) (x : PreTilt A p) :
    (_root_.frobeniusEquiv (PreTilt A p) p).symm (g • x) =
      g • (_root_.frobeniusEquiv (PreTilt A p) p).symm x :=
  (RingHom.map_frobeniusEquiv_symm p (MulSemiringAction.toRingHom G (PreTilt A p) g) x).symm

/-- The action of `G` commutes with the `p ^ n`-th root maps of the perfect ring `A♭`. -/
theorem iterate_frobeniusEquiv_symm_smul (g : G) (x : PreTilt A p) (n : ℕ) :
    (_root_.frobeniusEquiv (PreTilt A p) p).symm^[n] (g • x) =
      g • (_root_.frobeniusEquiv (PreTilt A p) p).symm^[n] x :=
  Function.Commute.iterate_left (f := (_root_.frobeniusEquiv (PreTilt A p) p).symm)
    (g := (g • ·)) (frobeniusEquiv_symm_smul g) n x

/-- **The sharp map is equivariant**: `(g • x)♯ = g • x♯` for a `p`-adically complete ring `A`. -/
@[simp]
theorem untilt_smul [IsAdicComplete (Ideal.span {(p : A)}) A] (g : G) (x : PreTilt A p) :
    (g • x).untilt = g • x.untilt :=
  untilt_natural _ x

section FractionRing

variable {G : Type*} [Group G] [MulSemiringAction G A] [IsDomain (PreTilt A p)]

/-- A group acting on `A` by ring automorphisms acts on the fraction field `Frac(A♭)` of its tilt
by field automorphisms, extending its action on `A♭` (Mathlib's
`IsFractionRing.mulSemiringAction`), when `A♭` is a domain, for instance when `A` is a `p`-adically
complete domain (`PreTilt.instIsDomain`). -/
noncomputable instance instMulSemiringActionFractionRing :
    MulSemiringAction G (FractionRing (PreTilt A p)) :=
  IsFractionRing.mulSemiringAction G (PreTilt A p) (FractionRing (PreTilt A p))

/-- The action of `G` on `Frac(A♭)` extends its action on `A♭`. -/
@[simp]
theorem smul_algebraMap_fractionRing (g : G) (x : PreTilt A p) :
    g • algebraMap (PreTilt A p) (FractionRing (PreTilt A p)) x =
      algebraMap (PreTilt A p) (FractionRing (PreTilt A p)) (g • x) :=
  (algebraMap.coe_smul' g x _).symm

/-- The inclusion `W(A♭) → W(Frac(A♭))` is equivariant. -/
theorem map_algebraMap_fractionRing_smul (g : G) (x : WittVector p (PreTilt A p)) :
    WittVector.map (algebraMap (PreTilt A p) (FractionRing (PreTilt A p))) (g • x) =
      g • WittVector.map (algebraMap (PreTilt A p) (FractionRing (PreTilt A p))) x :=
  WittVector.map_smul_of_map_smul (fun g x ↦ (smul_algebraMap_fractionRing g x).symm) g x

end FractionRing

end PreTilt

namespace WittVector

variable {G A : Type*} [Monoid G] [CommRing A] [MulSemiringAction G A] {p : ℕ} [Fact p.Prime]
  [Fact ¬IsUnit (p : A)] [IsAdicComplete (Ideal.span {(p : A)}) A]

/-- **Fontaine's map is equivariant**: `θ (g • w) = g • θ w` for `w ∈ W(A♭)`, where `G` acts on
the `p`-adically complete ring `A` by ring endomorphisms. -/
@[simp]
theorem fontaineTheta_smul (g : G) (w : WittVector p (PreTilt A p)) :
    fontaineTheta A p (g • w) = g • fontaineTheta A p w := by
  rw [smul_def, PreTilt.toRingHom_eq_map, theta_natural, MulSemiringAction.toRingHom_apply]

end WittVector

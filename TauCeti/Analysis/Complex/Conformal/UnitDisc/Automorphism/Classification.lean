/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import TauCeti.Analysis.Complex.Conformal.UnitDisc.Automorphism.Rotation

/-!
# Classification of holomorphic automorphisms of the complex unit disc

This file completes the classification of the holomorphic automorphisms of the open unit disc.
If `f` and `g` are mutually inverse holomorphic self-maps of the disc, then on the disc

`f z = u * (z - a) / (1 - conj a * z)`

for a unique center `a = g 0` and some `u` of modulus one.  The proof conjugates `f` by the
Moebius factor that sends `a` to the origin, then applies the origin-fixing rotation theorem
`exists_eqOn_const_mul_of_leftInvOn_ball_of_map_zero`.

This discharges the conformal-mapping roadmap's L2 description of the disc automorphism group
`Aut(𝔻) = {e^{iθ}(z−a)/(1−āz)}`.  It builds on Mathlib's Schwarz lemma and on the standard
disc-Moebius API developed in Tau Ceti.  As with the other L0--L3 conformal-mapping material,
this statement is coordinated with the upstream Mathlib Riemann-mapping effort
leanprover-community/mathlib4#33505 and should be replaced by human-curated upstream API if a
disc-automorphism classification lands there.
-/

public section

namespace TauCeti

open Complex Metric Set
open scoped ComplexConjugate

variable {f g : ℂ → ℂ}

private noncomputable abbrev discMoebiusFormula (a z : ℂ) : ℂ :=
  (z - a) / (1 - (starRingEnd ℂ) a * z)

private lemma differentiableOn_discMoebiusFormula {a : ℂ} (ha : ‖a‖ < 1) :
    DifferentiableOn ℂ (discMoebiusFormula a) (ball (0 : ℂ) 1) := by
  simpa only [discMoebiusFormula] using
    differentiableOn_unitDiscMoebiusFormula_of_norm_lt_one ha

private lemma mapsTo_ball_discMoebiusFormula {a : ℂ} (ha : ‖a‖ < 1) :
    MapsTo (discMoebiusFormula a) (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) := by
  simpa only [discMoebiusFormula] using
    mapsTo_ball_unitDiscMoebiusFormula_of_norm_lt_one ha

private lemma leftInvOn_discMoebiusFormula {a : ℂ} (ha : ‖a‖ < 1) :
    LeftInvOn (discMoebiusFormula (-a)) (discMoebiusFormula a) (ball (0 : ℂ) 1) := by
  simpa only [discMoebiusFormula] using
    leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one ha

private lemma rightInvOn_discMoebiusFormula {a : ℂ} (ha : ‖a‖ < 1) :
    RightInvOn (discMoebiusFormula (-a)) (discMoebiusFormula a) (ball (0 : ℂ) 1) := by
  simpa only [discMoebiusFormula, neg_neg] using
    leftInvOn_unitDiscMoebiusFormula_of_norm_lt_one (a := -a) (by simpa using ha)

/--
**Classification of holomorphic disc automorphisms.** Mutually inverse holomorphic self-maps
`f` and `g` of the open unit disc have the standard form
`f z = u * (z - a) / (1 - conj a * z)` on the disc, where the center is `a = g 0` and the
rotation factor `u` lies on the unit circle.
-/
theorem exists_eqOn_unitDiscStandardAutomorphismFormula
    (hf : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hg : DifferentiableOn ℂ g (ball (0 : ℂ) 1))
    (hfmaps : MapsTo f (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgmaps : MapsTo g (ball (0 : ℂ) 1) (ball (0 : ℂ) 1))
    (hgf : LeftInvOn g f (ball (0 : ℂ) 1))
    (hfg : LeftInvOn f g (ball (0 : ℂ) 1)) :
    ∃ (u : Circle) (a : Complex.UnitDisc), (a : ℂ) = g 0 ∧
      EqOn f (fun z => (u : ℂ) *
        ((z - (a : ℂ)) / (1 - (starRingEnd ℂ) (a : ℂ) * z)))
        (ball (0 : ℂ) 1) := by
  have hzero : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by
    rw [mem_ball_zero_iff]
    norm_num
  have ha_mem : g 0 ∈ ball (0 : ℂ) 1 := hgmaps hzero
  have ha : ‖g 0‖ < 1 := by simpa [mem_ball_zero_iff] using ha_mem
  have hfa : f (g 0) = 0 := hfg hzero
  let F : ℂ → ℂ := f ∘ discMoebiusFormula (-(g 0))
  let G : ℂ → ℂ := discMoebiusFormula (g 0) ∘ g
  have hneg : ‖-(g 0)‖ < 1 := by simpa using ha
  have hFdiff : DifferentiableOn ℂ F (ball (0 : ℂ) 1) :=
    hf.comp (differentiableOn_discMoebiusFormula hneg)
      (mapsTo_ball_discMoebiusFormula hneg)
  have hGdiff : DifferentiableOn ℂ G (ball (0 : ℂ) 1) :=
    (differentiableOn_discMoebiusFormula ha).comp hg hgmaps
  have hFmaps : MapsTo F (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    hfmaps.comp (mapsTo_ball_discMoebiusFormula hneg)
  have hGmaps : MapsTo G (ball (0 : ℂ) 1) (ball (0 : ℂ) 1) :=
    (mapsTo_ball_discMoebiusFormula ha).comp hgmaps
  have hGF : LeftInvOn G F (ball (0 : ℂ) 1) := by
    intro z hz
    rw [show G (F z) = discMoebiusFormula (g 0) (g (f (discMoebiusFormula (-(g 0)) z))) by
      rfl]
    rw [hgf ((mapsTo_ball_discMoebiusFormula hneg) hz)]
    exact rightInvOn_discMoebiusFormula ha hz
  have hFzero : F 0 = 0 := by
    rw [show F 0 = f (discMoebiusFormula (-(g 0)) 0) by rfl,
      discMoebiusFormula]
    simpa [ha.ne] using hfa
  obtain ⟨u, hu, hFu⟩ :=
    exists_eqOn_const_mul_of_leftInvOn_ball_of_map_zero hFdiff hGdiff hFmaps hGmaps hGF hFzero
  refine ⟨⟨u, by simpa [Submonoid.unitSphere] using hu⟩,
    Complex.UnitDisc.mk (g 0) ha, Complex.UnitDisc.coe_mk _ _, fun z hz => ?_⟩
  have hMz : discMoebiusFormula (g 0) z ∈ ball (0 : ℂ) 1 :=
    mapsTo_ball_discMoebiusFormula ha hz
  have hF := hFu hMz
  rw [show F (discMoebiusFormula (g 0) z) =
      f (discMoebiusFormula (-(g 0)) (discMoebiusFormula (g 0) z)) by rfl,
    leftInvOn_discMoebiusFormula ha hz] at hF
  simpa only [discMoebiusFormula, Complex.UnitDisc.coe_mk] using hF

end TauCeti

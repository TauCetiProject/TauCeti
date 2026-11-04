/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.UniformTilt.Tate
public import TauCeti.RingTheory.Perfectoid.PseudoUniformizerRoots.Gauge

/-!
# The spectral gauge under the sharp map

A pseudouniformiser with compatible roots in a complete uniform Tate ring `B` determines a
pseudouniformiser in its tilt. Shifting the compatible sequence gives the roots of this tilted
parameter. For these parameters the sharp map preserves the spectral gauge, even when `B` is
not perfectoid. In particular, the spectral gauge of a perfectoid ring pulls back to the
spectral gauge of its tilt.

The comparison uses the description of gauge balls as fractional powers of the parameter times
the power-bounded subring. Sharp preserves these fractional powers and detects power-boundedness;
it need not preserve addition. The comparison includes zero rings.

## References

* P. Scholze, *Perfectoid spaces*, proof of Lemma 5.21.
* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory II: imperfect period rings*,
  proof of Theorem 3.3.8.
-/

public section

open TauCeti.Huber

namespace TauCeti.Perfectoid

variable {p : ℕ} [hp : Fact p.Prime] {B : Type*} [CommRing B] [UniformSpace B]
  [IsUniformAddGroup B] [IsTopologicalRing B] [IsTateRing B] [CompleteSpace B] [T2Space B]
  [IsUniform B] [Fact (IsTopologicallyNilpotent (p : B))]

namespace PseudoUniformizerRoots

/-- A compatible-root parameter viewed as an element of the tilt. -/
def toTilt (ϖ : PseudoUniformizerRoots p B) : uniformTilt p B :=
  uniformTilt.mk ϖ.root ϖ.root_succ_pow

/-- Every coordinate of the tilted parameter is the corresponding root. -/
@[simp]
theorem coeff_toTilt (ϖ : PseudoUniformizerRoots p B) (n : ℕ) :
    uniformTilt.coeff p B n ϖ.toTilt = ϖ.root n :=
  uniformTilt.coeff_mk _ _ _

/-- The tilted parameter is a pseudouniformiser, since its sharp is one. -/
theorem isPseudoUniformizer_toTilt (ϖ : PseudoUniformizerRoots p B) :
    IsPseudoUniformizer ϖ.toTilt :=
  isPseudoUniformizer_iff.mpr
    ⟨uniformTilt.isUnit_iff_coeff_zero.mpr (by simpa using ϖ.isPseudoUniformizer.isUnit),
      uniformTilt.isTopologicallyNilpotent_iff_coeff_zero.mpr
        (by simpa using ϖ.isPseudoUniformizer.isTopologicallyNilpotent)⟩

variable [NonarchimedeanRing (uniformTilt p B)]

/-- The roots of the tilted parameter, obtained by shifting the original sequence.
An ambient Tate-ring instance can be supplied by `uniformTilt.isTateRing_of_sharp`. -/
noncomputable def tiltRoots (ϖ : PseudoUniformizerRoots p B) :
    PseudoUniformizerRoots p (uniformTilt p B) where
  roots := Perfection.liftMonoidHom p (uniformTilt p B) (uniformTilt p B)
    (MonoidHom.id _) ϖ.toTilt
  isPseudoUniformizer := by
    simpa only [Perfection.coeffMonoidHom_zero_liftMonoidHom, MonoidHom.id_apply] using
      ϖ.isPseudoUniformizer_toTilt
  pow_dvd := by
    have hz : (p : uniformTilt p B) = 0 := by
      rcases subsingleton_or_nontrivial B with hB | hB
      · exact uniformTilt.ext fun _ ↦ Subsingleton.elim _ _
      · exact CharP.cast_eq_zero _ p
    have hz' : (p : powerBoundedSubring (uniformTilt p B)) = 0 := Subtype.ext hz
    rw [hz']
    exact dvd_zero _

/-- The `m`-th coordinate of the `n`-th root of the tilted parameter is the `(n+m)`-th
root of the original parameter. -/
@[simp]
theorem coeff_tiltRoots_root (ϖ : PseudoUniformizerRoots p B) (n m : ℕ) :
    uniformTilt.coeff p B m (ϖ.tiltRoots.root n) = ϖ.root (n + m) := by
  have hpow : ϖ.tiltRoots.root n ^ p ^ n = ϖ.toTilt := by
    rw [← coeffMonoidHom_roots, Perfection.coeffMonoidHom_pow_p_pow_self,
      tiltRoots, Perfection.coeffMonoidHom_zero_liftMonoidHom, MonoidHom.id_apply]
  have hcoeff := congrArg (uniformTilt.coeff p B (m + n)) hpow
  rw [map_pow, uniformTilt.coeff_pow_p_pow, coeff_toTilt] at hcoeff
  simpa only [Nat.add_comm] using hcoeff

/-- The tilted root system starts at the original compatible sequence. -/
@[simp]
theorem tiltRoots_root_zero (ϖ : PseudoUniformizerRoots p B) :
    ϖ.tiltRoots.root 0 = ϖ.toTilt := by
  apply uniformTilt.ext
  intro n
  simp

end PseudoUniformizerRoots

namespace uniformTilt

section FractionalPowers

variable [NonarchimedeanRing (uniformTilt p B)]

/-- Sharp preserves fractional powers of compatible-root parameters whose roots have matching
zeroth coordinates. -/
theorem coeff_zero_zpow (ϖ : PseudoUniformizerRoots p B)
    (ψ : PseudoUniformizerRoots p (uniformTilt p B))
    (h : ∀ n, coeff p B 0 (ψ.root n) = ϖ.root n) (m : ℤ) (n : ℕ) :
    coeff p B 0 (ψ.zpow m n : uniformTilt p B) = (ϖ.zpow m n : B) := by
  have hu : Units.map (coeff p B 0) (ψ.unitRoot n) = ϖ.unitRoot n := by
    apply Units.ext
    simpa using h n
  have he := congrArg Units.val (congrArg (fun u : Bˣ ↦ u ^ m) hu)
  simpa only [PseudoUniformizerRoots.zpow_def, ← map_zpow, Units.coe_map] using he

end FractionalPowers

variable [IsTateRing (uniformTilt p B)] [IsUniform (uniformTilt p B)]

/-- **The spectral gauge is preserved by sharp.** The root systems need only agree after
applying sharp; no perfectoid hypothesis on the original ring is needed. -/
theorem gauge_sharp (ϖ : PseudoUniformizerRoots p B)
    (ψ : PseudoUniformizerRoots p (uniformTilt p B))
    (h : ∀ n, coeff p B 0 (ψ.root n) = ϖ.root n) (x : uniformTilt p B) :
    ϖ.gauge (coeff p B 0 x) = ψ.gauge x := by
  have hψ : IsPseudoUniformizer (coeff p B 0 (ψ.root 0)) := by
    rw [h]
    exact ϖ.isPseudoUniformizer_root_zero
  rw [ϖ.gauge_eq_sInf hp.out.one_lt, ψ.gauge_eq_sInf hp.out.one_lt]
  congr 2
  ext q
  simp only [Set.mem_ofPred_eq, ← coeff_zero_zpow ϖ ψ h, ← map_mul]
  exact (mem_powerBoundedSubring_iff hψ).symm

/-- For the canonical shifted roots in the tilt, sharp preserves the spectral gauges
normalised by the original parameter and its tilt. This does not assert preservation of distances:
sharp need not be additive or injective. -/
@[simp]
theorem gauge_sharp_tiltRoots (ϖ : PseudoUniformizerRoots p B) (x : uniformTilt p B) :
    ϖ.gauge (coeff p B 0 x) = ϖ.tiltRoots.gauge x := by
  exact gauge_sharp ϖ ϖ.tiltRoots (fun n ↦ by simp) x

end uniformTilt

end TauCeti.Perfectoid

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicSpace.Spa.HuberPair
public import TauCeti.AlgebraicGeometry.AdicSpace.ValuationSpectrum.LyingOver
public import TauCeti.RingTheory.Huber.ModuleTopology.Pair
public import Mathlib.RingTheory.RingHom.FaithfullyFlat
import Mathlib.Topology.Algebra.Algebra
import TauCeti.RingTheory.Valuation.Continuous.TopologicallyNilpotent
import TauCeti.RingTheory.Valuation.Integral.Basic

/-!
# The adic spectrum of a finite algebra over a Tate ring

Let `A` be a Tate ring, `A⁺ ⊆ A` a subring, and `B` a finite `A`-algebra with its natural
topology (`IsModuleTopology A B`). Write `B⁺` for the integral closure of the image of `A⁺` in
`B`, the plus ring of `TauCeti.Huber.Pair.finiteAlgebra` when `A⁺` is open. This file shows that a
point `w` of `Spv B` lies in `Spa(B, B⁺)` exactly when its pullback lies in `Spa(A, A⁺)`; in other
words `Spa(B, B⁺)` is the full preimage of `Spa(A, A⁺)` in `Spv B`. Combined with the lifting of
points of valuation spectra along primes lying over their supports
(`TauCeti.ValuationSpectrum.exists_supp_eq_comap_eq`), it follows that
`Spa(B, B⁺) → Spa(A, A⁺)` hits every point whose support is the contraction of a prime of `B`. In
particular it is surjective when `B` is faithfully flat over `A`, which is the surjectivity clause
of the Huber pair of a finite étale algebra.

The content is the continuity of `w` given that of its pullback. Fix a pseudouniformiser `ϖ` of
`A`. The integers of the pullback of `w` form an open subring of `A`, so the integral closure `C`
of their image is open in `B` (`TauCeti.Huber.isOpen_integralClosure_map_algebraMap`) and `w ≤ 1`
on it. Hence the translates of `ϖᴺ C` are neighbourhoods on which `w` is at most `w(ϖ)ᴺ`. It
remains to see that the powers of `w(ϖ)` are cofinal at every `c ∈ B` with `w(c) ≠ 0`, which
holds because `B` is integral over `A` (`Valuation.exists_pow_lt_of_isIntegral`).

## Main results

* `TauCeti.ValuationSpectrum.isContinuous_of_isContinuous_comap`: a valuation on `B` whose pullback
  to `A` is continuous is continuous.
* `TauCeti.ValuationSpectrum.mem_spa_integralClosure_iff`: `w ∈ Spa(B, B⁺)` iff its pullback lies
  in `Spa(A, A⁺)`.
* `TauCeti.ValuationSpectrum.exists_mem_spa_supp_eq_comap_eq`: a point of `Spa(A, A⁺)` lifts to
  `Spa(B, B⁺)` with any prescribed support lying over its own.
* `TauCeti.Huber.Pair.Hom.IsFiniteEtale.surjective_spaComap`: a faithfully flat finite étale
  morphism of Huber pairs over a Tate ring is surjective on adic spectra.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  §2.4, Remark 2.4.2.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §7, Definition 7.1 and
  Lemma 7.3.
* [T. Wedhorn, *Adic Spaces*][wedhorn_adic] (arXiv:1910.05934v1), Definition 7.23.
-/

public section

open Filter Topology TauCeti.Huber

namespace TauCeti

namespace ValuationSpectrum

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [CommRing B] [TopologicalSpace B] [Algebra A B] [Module.Finite A B] [IsModuleTopology A B]
  {Aplus : Subring A}

/-- **Continuity of a valuation on a finite algebra over a Tate ring.** If `B` is a finite
`A`-algebra with its natural topology and the pullback of `w ∈ Spv B` to `A` is continuous, then
`w` is continuous. -/
theorem isContinuous_of_isContinuous_comap {w : Spv B}
    (hw : (comap (algebraMap A B) w).IsContinuous) : w.IsContinuous := by
  have : IsTopologicalRing B := IsModuleTopology.isTopologicalRing A B
  set V := w.valuation
  set ι := algebraMap A B
  obtain ⟨ϖ, hϖ⟩ := IsTateRing.exists_isPseudoUniformizer (A := A)
  have hιϖ : IsPseudoUniformizer (ι ϖ) := hϖ.map (continuous_algebraMap A B)
  have hϖ0 : V (ι ϖ) ≠ 0 := (hιϖ.isUnit.map V).ne_zero
  -- the pullback of `V` to `A` is continuous
  have hu : (V.comap ι).IsContinuous := by
    rw [isContinuous_def] at hw
    refine (Valuation.IsEquiv.isContinuous_iff fun x y ↦ ?_).mp hw
    rw [valuation_le_iff, comap_vle, ← valuation_le_iff, Valuation.comap_apply,
      Valuation.comap_apply]
  -- the integers `A⁺` of the pullback form an open subring of `A`
  set Aplus := (V.comap ι).integer
  have hAplus : IsOpen (Aplus : Set A) := by
    simpa [Aplus, Valuation.integer] using hu.isOpen_le (b := 1) (by simp)
  -- `V ≤ 1` on the open ring `B⁺`, the integral closure of the image of `A⁺`
  set Bplus := (integralClosure (Aplus.map ι) B).toSubring
  have hle : ∀ b ∈ Bplus, V b ≤ 1 := fun b hb ↦ by
    refine (Subring.integralClosure_subring_le_iff (T := V.integer)).mpr ?_ hb
    rintro _ ⟨a, ha, rfl⟩
    exact ha
  have hBplus : IsOpen (Bplus : Set B) := isOpen_integralClosure_map_algebraMap hAplus
  -- a power of `ι ϖ` pushes every element into `B⁺`
  have habs (b : B) : ∃ m : ℕ, V (ι ϖ) ^ m * V b ≤ 1 := by
    obtain ⟨m, hm⟩ :=
      exists_mul_pow_mem_of_isTopologicallyNilpotent hιϖ.isTopologicallyNilpotent hBplus b
    exact ⟨m, by simpa [mul_comm] using hle _ hm⟩
  -- each `{b | V b < V c}` contains a translate of the open set `ϖᴺ B⁺` around each of its points
  rw [isContinuous_def, Valuation.isContinuous_iff_forall_ne_zero]
  intro c hc
  obtain ⟨N, hN⟩ :=
    Valuation.exists_pow_lt_of_isIntegral hu hϖ.isTopologicallyNilpotent hϖ0 habs hc
  obtain ⟨u, hιu⟩ := hιϖ.isUnit
  refine isOpen_iff_mem_nhds.mpr fun b₀ hb₀ ↦ ?_
  have hmem : {x : B | ((u⁻¹ : Bˣ) : B) ^ N * (x - b₀) ∈ Bplus} ∈ 𝓝 b₀ :=
    (hBplus.preimage (by fun_prop)).mem_nhds (by simp [Bplus.zero_mem])
  filter_upwards [hmem] with x hx
  have hx' : V (x - b₀) ≤ V (ι ϖ) ^ N := by
    calc V (x - b₀) = V (ι ϖ) ^ N * V (((u⁻¹ : Bˣ) : B) ^ N * (x - b₀)) := by
          rw [← map_pow, ← map_mul, ← mul_assoc, ← hιu, ← mul_pow, Units.mul_inv, one_pow,
            one_mul]
      _ ≤ V (ι ϖ) ^ N * 1 := by gcongr; exact hle _ hx
      _ = V (ι ϖ) ^ N := mul_one _
  rw [← add_sub_cancel b₀ x]
  exact V.map_add_lt hb₀ (hx'.trans_lt hN)

/-- **The adic spectrum of a finite algebra is the preimage of the base.** For a finite
`A`-algebra `B` with its natural topology over a Tate ring and a subring `A⁺`, a point
`w ∈ Spv B` lies in `Spa(B, B⁺)`, with `B⁺` the integral closure of the image of `A⁺`, exactly when
its pullback lies in `Spa(A, A⁺)`. -/
theorem mem_spa_integralClosure_iff {w : Spv B} :
    w ∈ spa (integralClosure (Aplus.map (algebraMap A B)) B).toSubring ↔
      comap (algebraMap A B) w ∈ spa Aplus := by
  rw [spa_integralClosure]
  refine ⟨comap_mem_spa (continuous_algebraMap A B) fun a ha ↦ Subring.mem_map.mpr ⟨a, ha, rfl⟩,
    fun hw ↦ ?_⟩
  exact (mem_spa_map_iff (continuous_algebraMap A B) Aplus
    (isContinuous_of_isContinuous_comap ((mem_spa_iff _ _).mp hw).1)).mpr hw

/-- **Lifting points of the adic spectrum to a finite algebra.** Over a Tate ring with a subring
`A⁺`, a point `v ∈ Spa(A, A⁺)` is the pullback of a point of `Spa(B, B⁺)` with support any
prime `𝔮` of `B` lying over `supp v`, where `B` is a finite `A`-algebra with its natural topology
and `B⁺` the integral closure of the image of `A⁺`. -/
theorem exists_mem_spa_supp_eq_comap_eq {v : Spv A} (hv : v ∈ spa Aplus) (q : Ideal B) [q.IsPrime]
    (hq : q.comap (algebraMap A B) = v.supp) :
    ∃ w ∈ spa (integralClosure (Aplus.map (algebraMap A B)) B).toSubring,
      w.supp = q ∧ comap (algebraMap A B) w = v := by
  obtain ⟨w, hwq, hwv⟩ := exists_supp_eq_comap_eq (algebraMap A B) v q hq
  exact ⟨w, mem_spa_integralClosure_iff.mpr (hwv ▸ hv), hwq, hwv⟩

end ValuationSpectrum

namespace Huber.Pair.Hom

open ValuationSpectrum

variable {A B : Type*} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsTateRing A]
  [CommRing B] [TopologicalSpace B] [IsTopologicalRing B] [IsHuberRing B] {S : Pair A}
  {T : Pair B}

/-- **A faithfully flat finite étale morphism of Huber pairs is surjective on adic spectra.** If
`φ : (A, A⁺) → (B, B⁺)` is finite étale over a Tate ring `A` and `B` is faithfully flat over `A`,
then `Spa(B, B⁺) → Spa(A, A⁺)` is surjective; `A` need not be complete. For finite algebras that
need not be étale or flat, `TauCeti.ValuationSpectrum.exists_mem_spa_supp_eq_comap_eq` lifts every
point whose support is contracted from a prime of `B`. -/
theorem IsFiniteEtale.surjective_spaComap {φ : Hom S T} (hφ : φ.IsFiniteEtale)
    (hff : φ.toRingHom.FaithfullyFlat) : Function.Surjective φ.spaComap := by
  intro x
  let := φ.toRingHom.toAlgebra
  have : Module.Finite A B := hφ.finite
  have : IsModuleTopology A B := hφ.isModuleTopology
  obtain ⟨q, hq⟩ := (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff).2 (suppFun x.1)
  obtain ⟨w, hw, -, hwx⟩ := exists_mem_spa_supp_eq_comap_eq x.2 q.asIdeal
    (by rw [← suppFun_asIdeal]; exact congrArg PrimeSpectrum.asIdeal hq)
  exact ⟨⟨w, hφ.plus_eq ▸ hw⟩, Subtype.ext <| by rw [spaComap_val]; exact hwx⟩

end Huber.Pair.Hom

end TauCeti

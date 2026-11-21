/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Frobenius
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.Flat
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.Algebra.ZMod
import Mathlib.FieldTheory.IsPerfectClosure
import Mathlib.FieldTheory.PerfectClosure
import TauCeti.RingTheory.AdicCompletion.Flat.Basic
import TauCeti.RingTheory.AdicCompletion.Flat.Frobenius
import TauCeti.RingTheory.AdicCompletion.Noetherian
import TauCeti.RingTheory.Flat.ProjectiveDimension
import TauCeti.RingTheory.LocalRing.CoefficientField
import TauCeti.RingTheory.Perfect.IsPRadical
import TauCeti.RingTheory.Perfect.PerfectClosure
import TauCeti.RingTheory.Perfect.Projective.Dimension
import TauCeti.RingTheory.RegularLocalRing.Descent
import TauCeti.RingTheory.RegularLocalRing.Frobenius
import TauCeti.RingTheory.RegularLocalRing.PowerSeries
import TauCeti.RingTheory.RegularLocalRing.ProjectiveDimension

/-!
# Kunz's theorem: flat Frobenius characterizes regularity

Let `R` be a Noetherian ring of prime characteristic `p`. If the Frobenius endomorphism
`x ↦ x ^ p` of `R` is flat, then `R` is a regular ring (`TauCeti.IsRegularRing.of_flat_frobenius`).
Together with the converse `TauCeti.IsRegularRing.flat_frobenius`, this is Kunz's
characterization of regular rings in characteristic `p`
(`TauCeti.isRegularRing_iff_flat_frobenius`).

We follow the proof of Bhatt–Scholze through perfection rather than Kunz's length count.

* Flatness of Frobenius localizes, so it suffices to treat a Noetherian local ring `R`. It passes
  to the completion `R̂` (`TauCeti.AdicCompletion.flat_frobenius`), and regularity descends from
  `R̂` along the faithfully flat map `R → R̂` (`TauCeti.IsRegularLocalRing.of_faithfullyFlat`), so
  we may assume that `R` is complete.
* By the Cohen structure theorem (`TauCeti.exists_surjective_mvPowerSeries_spanFinrank`), a
  complete Noetherian local ring of characteristic `p` is a quotient of a power series ring
  `P₀ = κ⟦x₁, …, x_e⟧` over its residue field, which is a regular local ring
  (`TauCeti.MvPowerSeries.isRegularLocalRing`).
* The perfection `R_perf` is then a perfect quotient of the perfection of the regular ring `P₀`,
  so every `R_perf`-module has projective dimension at most `dim P₀ + 1`
  (`IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective`).
* Because Frobenius of `R` is flat, so is `R → R_perf` (`RingHom.Flat.of_isPerfectClosure`), and
  this map is faithfully flat since it induces a homeomorphism of prime spectra. Projective
  dimension of finite modules over a Noetherian ring descends along faithfully flat maps
  (`ModuleCat.projectiveDimension_tensorProduct`), so the residue field of `R` has finite
  projective dimension, and `R` is regular by Serre's criterion
  (`TauCeti.isRegularLocalRing_iff_projectiveDimension_ne_top`).

## Main results

* `TauCeti.IsRegularLocalRing.of_flat_frobenius`: a Noetherian local ring of characteristic `p`
  with flat Frobenius is a regular local ring.
* `TauCeti.IsRegularRing.of_flat_frobenius`: a Noetherian ring of characteristic `p` with flat
  Frobenius is a regular ring.
* `TauCeti.isRegularLocalRing_iff_flat_frobenius`, `TauCeti.isRegularRing_iff_flat_frobenius`:
  **Kunz's theorem**, a Noetherian (local) ring of characteristic `p` is regular exactly when its
  Frobenius endomorphism is flat.

## References

* E. Kunz, *Characterizations of regular local rings of characteristic p*, Amer. J. Math. 91
  (1969), 772–784, Theorem 2.1.
* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*,
  Invent. Math. 209 (2017), Corollary 11.35 and its proof.
* [Stacks Project, Tag 0EC0](https://stacks.math.columbia.edu/tag/0EC0).
-/

public section

open IsLocalRing CategoryTheory

universe u

namespace TauCeti

variable {R : Type u} [CommRing R] (p : ℕ) [hp : Fact p.Prime] [CharP R p]

/-- The case of a complete local ring: through a Cohen presentation, the perfection of `R` is a
perfect quotient of the perfection of a regular local ring, so it has finite global dimension, and
this descends to the residue field of `R` along the faithfully flat map `R → R_perf`. -/
private theorem isRegularLocalRing_of_flat_frobenius_of_isAdicComplete [IsLocalRing R]
    [IsNoetherianRing R] [IsAdicComplete (maximalIdeal R) R] (h : (frobenius R p).Flat) :
    IsRegularLocalRing R := by
  -- A Cohen presentation `φ : κ⟦x₁, …, x_e⟧ → R` over the residue field `κ`.
  let := ZMod.algebra R p
  obtain ⟨s, -, φ, hφ, -, -⟩ :=
    exists_surjective_mvPowerSeries_spanFinrank (ZMod p) R (maximalIdeal R).fg_of_isNoetherianRing
  let P₀ := MvPowerSeries (Fin (maximalIdeal R).spanFinrank) (ResidueField R)
  have : CharP (ResidueField R) p := (RingHom.charP_iff_charP s p).2 inferInstance
  have : CharP P₀ p := charP_of_injective_algebraMap (algebraMap (ResidueField R) P₀).injective p
  -- The perfection of `φ` is a surjection onto `R_perf` from the perfection of a regular ring.
  let f : PerfectClosure P₀ p →+* PerfectClosure R p :=
    PerfectRing.lift (PerfectClosure.of P₀ p) ((PerfectClosure.of R p).comp φ) p
  have hf : Function.Surjective f := fun x ↦ by
    obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem (PerfectClosure.of R p) p x
    obtain ⟨z, rfl⟩ := hφ y
    refine ⟨(iterateFrobeniusEquiv (PerfectClosure P₀ p) p n).symm (PerfectClosure.of P₀ p z), ?_⟩
    apply (iterateFrobeniusEquiv (PerfectClosure R p) p n).injective
    rw [iterateFrobeniusEquiv_apply, iterateFrobeniusEquiv_apply, iterateFrobenius_def,
      iterateFrobenius_def, ← hy, ← map_pow, ← iterateFrobenius_def, ← iterateFrobeniusEquiv_apply,
      RingEquiv.apply_symm_apply]
    exact PerfectRing.lift_comp_apply _ _ p z
  have hd : ringKrullDim P₀ ≤ (maximalIdeal P₀).spanFinrank :=
    (IsRegularLocalRing.spanFinrank_maximalIdeal (R := P₀)).ge
  -- `R → R_perf` is faithfully flat.
  let := (PerfectClosure.of R p).toAlgebra
  have : Module.Flat R (PerfectClosure R p) :=
    RingHom.flat_algebraMap_iff.mp (RingHom.Flat.of_isPerfectClosure (PerfectClosure.of R p) p h)
  have : Module.FaithfullyFlat R (PerfectClosure R p) :=
    .of_comap_surjective (IsPRadical.isHomeomorph_comap (PerfectClosure.of R p) p).surjective
  have : Module.Finite R (Shrink.{u} (R ⧸ maximalIdeal R)) :=
    Module.Finite.equiv (Shrink.linearEquiv R _).symm
  refine isRegularLocalRing_iff_projectiveDimension_ne_top.mpr ?_
  rw [← ModuleCat.projectiveDimension_tensorProduct (PerfectClosure R p)]
  exact (projectiveDimension_ne_top_iff _).mpr ⟨_,
    IsPerfectClosure.hasProjectiveDimensionLE_succ_of_isRegularRing_of_surjective
      (PerfectClosure.of P₀ p) p hd hf _⟩

/-- **The converse of Kunz's theorem, local form.** A Noetherian local ring of prime
characteristic `p` whose Frobenius endomorphism is flat is a regular local ring. -/
@[stacks 0EC0 "flatness of Frobenius implies regularity"]
theorem IsRegularLocalRing.of_flat_frobenius [IsLocalRing R] [IsNoetherianRing R]
    (h : (frobenius R p).Flat) : IsRegularLocalRing R := by
  -- Pass to the completion, which is faithfully flat over `R` and has flat Frobenius.
  have : CharP (AdicCompletion (maximalIdeal R) R) p :=
    (expChar_prime_iff (R := AdicCompletion (maximalIdeal R) R) hp.out).1 inferInstance
  have := isRegularLocalRing_of_flat_frobenius_of_isAdicComplete p
    (AdicCompletion.flat_frobenius p h)
  exact IsRegularLocalRing.of_faithfullyFlat (S := AdicCompletion (maximalIdeal R) R)

/-- **The converse of Kunz's theorem.** A Noetherian ring of prime characteristic `p` whose
Frobenius endomorphism is flat is a regular ring (Bhatt–Scholze, Corollary 11.35). -/
@[stacks 0EC0 "flatness of Frobenius implies regularity"]
theorem IsRegularRing.of_flat_frobenius [IsNoetherianRing R] (h : (frobenius R p).Flat) :
    IsRegularRing R := by
  refine isRegularRing_iff.mpr fun J _ ↦ ?_
  have : CharP (Localization.AtPrime J) p := (CharP.charP_iff_prime_eq_zero hp.out).2 <| by
    rw [← map_natCast (algebraMap R _), CharP.cast_eq_zero, map_zero]
  -- Frobenius of `R_J` is induced by Frobenius of `R`, since `a ^ p ∈ J` exactly when `a ∈ J`.
  have hQ : J = J.comap (frobenius R p) := by
    ext a
    exact (‹J.IsPrime›.pow_mem_iff_mem p hp.out.pos).symm
  have hcomp : Localization.localRingHom J J (frobenius R p) hQ =
      frobenius (Localization.AtPrime J) p :=
    IsLocalization.ringHom_ext J.primeCompl <| RingHom.ext fun a ↦ by
      simp [Localization.localRingHom_to_map, frobenius_def]
  exact IsRegularLocalRing.of_flat_frobenius p (hcomp ▸ h.localRingHom J J hQ)

/-- **Kunz's theorem, local form.** A Noetherian local ring of prime characteristic `p` is a
regular local ring exactly when its Frobenius endomorphism is flat. -/
@[stacks 0EC0]
theorem isRegularLocalRing_iff_flat_frobenius [IsLocalRing R] [IsNoetherianRing R] :
    IsRegularLocalRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularLocalRing.flat_frobenius p, IsRegularLocalRing.of_flat_frobenius p⟩

/-- **Kunz's theorem.** A Noetherian ring of prime characteristic `p` is a regular ring exactly
when its Frobenius endomorphism is flat (Kunz, Theorem 2.1). -/
@[stacks 0EC0]
theorem isRegularRing_iff_flat_frobenius [IsNoetherianRing R] :
    IsRegularRing R ↔ (frobenius R p).Flat :=
  ⟨fun _ ↦ IsRegularRing.flat_frobenius p, IsRegularRing.of_flat_frobenius p⟩

end TauCeti

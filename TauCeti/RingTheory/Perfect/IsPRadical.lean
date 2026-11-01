/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.FieldTheory.IsPerfectClosure
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph

/-!
# Spectra of `p`-radical ring maps and maps into perfect rings

A ring map `i : K →+* L` is `p`-radical (Mathlib's `IsPRadical i p`) if some `p ^ n`-th power of
every element of `L` lies in the image of `K` and the kernel of `i` consists of `p`-nilpotent
elements. The basic example is the colimit perfection `PerfectClosure K p` of a ring `K` of
characteristic `p`.

This file records the facts about `p`-radical maps that make `Spec L → Spec K` behave like a
perfection: `i` is integral, it induces a homeomorphism of prime spectra, and when `p = 0` in `K`
every ring map from `K` to a perfect ring extends uniquely along `i`. Unlike Mathlib's
`PerfectRing.liftEquiv`, the last statement assumes no `ExpChar` instances, so it applies to the
zero ring, which is perfect but has no exponential characteristic. This is the form needed for the
ring of global sections of a perfect scheme, which is the zero ring for the empty scheme.

## Main results

* `IsPRadical.isIntegral`: a `p`-radical ring map is integral.
* `IsPRadical.isHomeomorph_comap`: a `p`-radical ring map induces a homeomorphism of prime spectra.
* `IsPRadical.bijective_comp`: if `p = 0` in `K` and `M` is a perfect ring, then precomposition
  with a `p`-radical map `i : K →+* L` is a bijection `(L →+* M) → (K →+* M)`.

## References

* B. Bhatt and P. Scholze, *Projectivity of the Witt vector affine Grassmannian*, Invent. Math.
  209 (2017), Section 3.
* The Stacks Project, [Tag 0BR8](https://stacks.math.columbia.edu/tag/0BR8), for the
  homeomorphism of spectra.
-/

public section

namespace IsPRadical

variable {K L M : Type*} [CommRing K] [CommRing L] [CommRing M] (i : K →+* L) (p : ℕ)
  [IsPRadical i p]

/-- **A `p`-radical ring map is integral**: every element of the target has a `p ^ n`-th power in
the image of the source. -/
theorem isIntegral [NeZero p] : i.IsIntegral := fun x ↦ by
  obtain ⟨n, y, hy⟩ := IsPRadical.pow_mem i p x
  let _ := i.toAlgebra
  exact IsIntegral.of_pow (pow_pos (Nat.pos_of_neZero p) n) (hy ▸ i.isIntegralElem_map)

/-- **A `p`-radical ring map induces a homeomorphism of prime spectra.** -/
theorem isHomeomorph_comap [NeZero p] : IsHomeomorph (PrimeSpectrum.comap i) :=
  PrimeSpectrum.isHomeomorph_comap i
    (fun x ↦ let ⟨n, y, hy⟩ := IsPRadical.pow_mem i p x
      ⟨p ^ n, pow_pos (Nat.pos_of_neZero p) n, y, hy⟩)
    ((IsPRadical.ker_le i p).trans pNilradical_le_nilradical)

/-- **Ring maps into a perfect ring extend uniquely along a `p`-radical map.** If `p = 0` in `K`
and `M` is a perfect ring, then `f ↦ f.comp i` is a bijection from `L →+* M` to `K →+* M`. The
ring `M` may be the zero ring. -/
theorem bijective_comp [hp : Fact p.Prime] (hK : (p : K) = 0) [PerfectRing M p] :
    Function.Bijective fun f : L →+* M ↦ f.comp i := by
  rcases subsingleton_or_nontrivial M with hM' | hM'
  · -- Over the zero ring, both sets of ring maps are singletons.
    refine ⟨fun f g _ ↦ RingHom.ext fun _ ↦ Subsingleton.elim _ _, fun j ↦ ?_⟩
    refine ⟨
      { toFun _ := 0
        map_one' := Subsingleton.elim _ _
        map_mul' _ _ := Subsingleton.elim _ _
        map_zero' := rfl
        map_add' _ _ := Subsingleton.elim _ _ }, RingHom.ext fun _ ↦ Subsingleton.elim _ _⟩
  -- Any ring map `K →+* M` forces `p = 0` in `M`.
  have hM (j : K →+* M) : CharP M p :=
    (CharP.charP_iff_prime_eq_zero hp.out).2 (by rw [← map_natCast j, hK, map_zero])
  refine ⟨fun f g hfg ↦ ?_, fun j ↦ ?_⟩
  · have := hM (f.comp i)
    exact IsPRadical.injective_comp_of_perfect M i p hfg
  have := hM j
  have : Nontrivial K := j.domain_nontrivial
  have : CharP K p := (CharP.charP_iff_prime_eq_zero hp.out).2 hK
  -- `L` is nonzero: otherwise `1` lies in the kernel of `i`, so `1` would be `p`-nilpotent.
  have : Nontrivial L := by
    refine (subsingleton_or_nontrivial L).resolve_left fun _ ↦ ?_
    obtain ⟨n, hn⟩ := mem_pNilradical.1
      (IsPRadical.ker_le i p ((RingHom.mem_ker (r := 1)).2 (Subsingleton.elim _ _)))
    simp at hn
  have : CharP L p :=
    (CharP.charP_iff_prime_eq_zero hp.out).2 (by rw [← map_natCast i, hK, map_zero])
  exact ⟨PerfectRing.lift i j p, PerfectRing.lift_comp i j p⟩

end IsPRadical

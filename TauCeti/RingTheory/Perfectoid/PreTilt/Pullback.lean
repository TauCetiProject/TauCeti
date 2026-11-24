/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.PreTilt.Map
public import TauCeti.RingTheory.Pullback

import TauCeti.RingTheory.Perfectoid.Untilt

/-!
# Tilts of fibre products

Let `f : A →+* A'` and `g : B →+* A'` be ring homomorphisms and `C = A ×_{A'} B` their fibre
product (Mathlib's `RingHom.pullback f g`). The projections induce a ring homomorphism of tilts
`C♭ → A♭ ×_{A'♭} B♭` into the fibre product of `PreTilt.map p f` and `PreTilt.map p g`. When
`A`, `B`, `A'` and `C` are `p`-adically complete, it is an isomorphism (`PreTilt.pullbackEquiv`).

For a `p`-adically complete ring `X`, an element `x ∈ X♭` is determined by the sharps
`((x ^ (1 / p ^ n))♯)ₙ`, a compatible system of `p`-th roots in `X` whose reductions modulo `p` are
the coordinates of `x` (`PreTilt.coeff_eq_mk_untilt_iterate`), and the sharp map is natural
(`PreTilt.untilt_natural`). Given `a ∈ A♭` and `b ∈ B♭` with the same image in `A'♭`, the pairs
`((a ^ (1 / p ^ n))♯, (b ^ (1 / p ^ n))♯)` therefore form a compatible system of `p`-th roots in
`C`, whose reduction modulo `p` is a preimage of `(a, b)`; and an element of `C♭` is determined by
the sharps of its roots, whose components in `A` and `B` are the sharps of its images. Only the
injectivity uses the completeness of `C`.

The fibre product `C` is `p`-adically complete when `A` and `B` are, `A'` is `p`-adically
separated and the `p`-power torsion of `A'` is bounded
(`RingHom.isAdicComplete_span_natCast_pullback`); for instance when `A'[p ^ ∞] = A'[p]`, as for
integral perfectoid rings.

## Main definitions

* `PreTilt.pullbackEquiv`: `(A ×_{A'} B)♭ ≃+* A♭ ×_{A'♭} B♭`, induced by the projections.

## Main results

* `PreTilt.coe_pullbackEquiv_apply`: the components of the isomorphism are the maps of tilts
  induced by the projections.
* `PreTilt.coe_untilt_pullbackEquiv_symm`: the sharp of the element of `C♭` corresponding to
  `(a, b)` is `(a♯, b♯)`.

## References

* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, §2.1.1, and the proof of
  Proposition 2.1.4, second paragraph.
-/

public section

open Ideal

variable {A B A' : Type*} [CommRing A] [CommRing B] [CommRing A']

/-- A fibre product `A ×_{A'} B` is a ring in which `p` is not a unit as soon as `p` is not a unit
in `A`. -/
instance RingHom.fact_not_isUnit_natCast_pullback (f : A →+* A') (g : B →+* A') (p : ℕ)
    [Fact ¬IsUnit (p : A)] :
    Fact ¬IsUnit (p : f.pullback g) :=
  ⟨fun h ↦ Fact.out (p := ¬IsUnit (p : A)) <| by simpa using h.map (f.pullbackFst g)⟩

namespace PreTilt

variable (p : ℕ) [Fact p.Prime] [Fact ¬IsUnit (p : A)] [Fact ¬IsUnit (p : B)]
  [Fact ¬IsUnit (p : A')] (f : A →+* A') (g : B →+* A')

variable [IsAdicComplete (span {(p : A)}) A] [IsAdicComplete (span {(p : B)}) B]

/-- The homomorphism of tilts `(A ×_{A'} B)♭ → A♭ ×_{A'♭} B♭` induced by the projections. -/
private noncomputable abbrev pullbackHom :
    PreTilt (f.pullback g) p →+* (map p f).pullback (map p g) :=
  (map p f).pullbackLift (map p g) (map p (f.pullbackFst g)) (map p (f.pullbackSnd g)) <| by
    rw [← map_comp, ← map_comp, f.pullback_comm_sq g]

omit [Fact ¬IsUnit (p : A')] in
/-- The sharp of an element of `(A ×_{A'} B)♭` is the pair of the sharps of its images. -/
private theorem coe_untilt_pullback [IsAdicComplete (span {(p : f.pullback g)}) (f.pullback g)]
    (x : PreTilt (f.pullback g) p) :
    (x.untilt : A × B) = ((map p (f.pullbackFst g) x).untilt, (map p (f.pullbackSnd g) x).untilt) :=
  Prod.ext (untilt_natural (f.pullbackFst g) x).symm (untilt_natural (f.pullbackSnd g) x).symm

/-- The comparison homomorphism is injective when the fibre product is `p`-adically complete: an
element of the tilt is determined by the sharps of its `p`-power roots. -/
private theorem pullbackHom_injective
    [IsAdicComplete (span {(p : f.pullback g)}) (f.pullback g)] :
    Function.Injective (pullbackHom p f g) := by
  intro x y hxy
  have h := Subtype.ext_iff.mp hxy
  simp only [RingHom.coe_pullbackLift_apply, Prod.mk.injEq] at h
  obtain ⟨h₁, h₂⟩ := h
  refine ext fun n ↦ ?_
  rw [coeff_eq_mk_untilt_iterate, coeff_eq_mk_untilt_iterate]
  congr 1
  refine Subtype.ext ?_
  rw [coe_untilt_pullback, coe_untilt_pullback, RingHom.map_iterate_frobeniusEquiv_symm,
    RingHom.map_iterate_frobeniusEquiv_symm, RingHom.map_iterate_frobeniusEquiv_symm,
    RingHom.map_iterate_frobeniusEquiv_symm, h₁, h₂]

variable [IsAdicComplete (span {(p : A')}) A']

/-- The comparison homomorphism is surjective: for `a ∈ A♭` and `b ∈ B♭` with the same image in
`A'♭`, the pairs of sharps of their `p`-power roots form a compatible system of `p`-th roots in the
fibre product, whose reduction modulo `p` is a preimage of `(a, b)`. -/
private theorem pullbackHom_surjective : Function.Surjective (pullbackHom p f g) := by
  rintro ⟨⟨a, b⟩, hab⟩
  have hab' : map p f a = map p g b := by simpa using hab
  -- the compatible system `((a ^ (1 / p ^ n))♯, (b ^ (1 / p ^ n))♯)ₙ` in the fibre product
  have hc (n : ℕ) : (untilt ((frobeniusEquiv (PreTilt A p) p).symm^[n] a),
      untilt ((frobeniusEquiv (PreTilt B p) p).symm^[n] b)) ∈ f.pullback g := by
    rw [RingHom.mem_eqLocus, RingHom.comp_apply, RingHom.comp_apply, RingHom.coe_fst,
      RingHom.coe_snd, ← untilt_natural, ← untilt_natural, RingHom.map_iterate_frobeniusEquiv_symm,
      RingHom.map_iterate_frobeniusEquiv_symm, hab']
  let c (n : ℕ) : f.pullback g := ⟨_, hc n⟩
  have hcp (n : ℕ) : Ideal.Quotient.mk (span {(p : f.pullback g)}) (c (n + 1)) ^ p =
      Ideal.Quotient.mk _ (c n) := by
    rw [← map_pow]
    congr 1
    exact Subtype.ext <| Prod.ext (untilt_iterate_frobeniusEquiv_symm_succ_pow a n)
      (untilt_iterate_frobeniusEquiv_symm_succ_pow b n)
  let x₀ : Perfection (ModP (f.pullback g) p) p := ⟨fun n ↦ Ideal.Quotient.mk _ (c n), hcp⟩
  obtain ⟨x, hx⟩ : ∃ x : PreTilt (f.pullback g) p, ∀ n, coeff n x = Ideal.Quotient.mk _ (c n) :=
    ⟨equivPerfection.symm x₀, fun n ↦ by rw [coeff_equivPerfection_symm, Perfection.coeff_mk]⟩
  refine ⟨x, Subtype.ext (Prod.ext (ext fun n ↦ ?_) (ext fun n ↦ ?_))⟩
  · rw [RingHom.coe_pullbackLift_apply, coeff_map, hx, ModP.map_mk, coeff_eq_mk_untilt_iterate]
    simp [c]
  · rw [RingHom.coe_pullbackLift_apply, coeff_map, hx, ModP.map_mk, coeff_eq_mk_untilt_iterate]
    simp [c]

variable [IsAdicComplete (span {(p : f.pullback g)}) (f.pullback g)]

private theorem pullbackHom_bijective : Function.Bijective (pullbackHom p f g) :=
  ⟨pullbackHom_injective p f g, pullbackHom_surjective p f g⟩

/-- **The tilt of a fibre product is the fibre product of the tilts.** For `p`-adically complete
rings `A`, `B`, `A'` and ring homomorphisms `f : A →+* A'`, `g : B →+* A'` whose fibre product
`A ×_{A'} B` is `p`-adically complete, the projections induce a ring isomorphism
`(A ×_{A'} B)♭ ≃+* A♭ ×_{A'♭} B♭`. -/
noncomputable def pullbackEquiv :
    PreTilt (f.pullback g) p ≃+* (map p f).pullback (map p g) :=
  RingEquiv.ofBijective (pullbackHom p f g) (pullbackHom_bijective p f g)

variable {p f g}

/-- `PreTilt.pullbackEquiv` sends `x` to the pair of its images under the maps of tilts induced by
the two projections. -/
@[simp]
theorem coe_pullbackEquiv_apply (x : PreTilt (f.pullback g) p) :
    (pullbackEquiv p f g x : PreTilt A p × PreTilt B p) =
      (map p (f.pullbackFst g) x, map p (f.pullbackSnd g) x) := by
  rw [pullbackEquiv, RingEquiv.ofBijective_apply, RingHom.coe_pullbackLift_apply]

/-- The sharp of the element of `(A ×_{A'} B)♭` corresponding to `(a, b) ∈ A♭ ×_{A'♭} B♭` is
`(a♯, b♯)`. -/
@[simp]
theorem coe_untilt_pullbackEquiv_symm (y : (map p f).pullback (map p g)) :
    (((pullbackEquiv p f g).symm y).untilt : A × B) =
      ((y : PreTilt A p × PreTilt B p).1.untilt, (y : PreTilt A p × PreTilt B p).2.untilt) := by
  have h := coe_pullbackEquiv_apply ((pullbackEquiv p f g).symm y)
  rw [RingEquiv.apply_symm_apply] at h
  rw [coe_untilt_pullback, h]

end PreTilt

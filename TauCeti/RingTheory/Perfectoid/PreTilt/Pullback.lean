/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.PreTilt.Map
public import TauCeti.RingTheory.Pullback

import Mathlib.NumberTheory.Basic

/-!
# Tilts of fibre products

Let `f : A →+* A'` and `g : B →+* A'` be ring homomorphisms and `C = A ×_{A'} B` their fibre
product (Mathlib's `RingHom.pullback f g`). The projections induce a ring homomorphism of tilts
`C♭ → A♭ ×_{A'♭} B♭` into the fibre product of `PreTilt.map p f` and `PreTilt.map p g`. When
`A`, `B` and `C` are `p`-adically complete and `A'` is `p`-adically separated, it is an isomorphism
(`PreTilt.pullbackEquiv`).

For a `p`-adically complete ring `X`, an element `x ∈ X♭` is determined by the sharps
`((x ^ (1 / p ^ n))♯)ₙ`, a compatible system of `p`-th roots in `X` whose reductions modulo `p` are
the coordinates of `x` (`PreTilt.coeff_eq_mk_untilt_iterate`), and the sharp map is natural
(`PreTilt.untilt_natural`). Given `a ∈ A♭` and `b ∈ B♭` with the same image in `A'♭`, the
elements `f ((a ^ (1 / p ^ n))♯)` and `g ((b ^ (1 / p ^ n))♯)` agree modulo `p`, so their
`p ^ n`-th powers `f (a♯)` and `g (b♯)` agree modulo `p ^ (n + 1)`; as `A'` is separated,
`f (a♯) = g (b♯)`. The pairs `((a ^ (1 / p ^ n))♯, (b ^ (1 / p ^ n))♯)` therefore form a
compatible system of `p`-th roots in `C`, whose reduction modulo `p` is a preimage of `(a, b)`; and
an element of `C♭` is determined by the sharps of its roots, whose components in `A` and `B` are
the sharps of its images. Only the injectivity uses the completeness of `C`.

The fibre product `C` is `p`-adically complete when `A` and `B` are, `A'` is `p`-adically
separated and the `p`-power torsion of `A'` is bounded
(`RingHom.isAdicComplete_span_natCast_pullback`); for instance when `A'[p ^ ∞] = A'[p]`, as for
integral perfectoid rings.

## Main definitions

* `PreTilt.pullbackEquiv`: `(A ×_{A'} B)♭ ≃+* A♭ ×_{A'♭} B♭`, induced by the projections.

## Main results

* `PreTilt.coe_pullbackEquiv_apply`, `PreTilt.pullbackFst_comp_pullbackEquiv`,
  `PreTilt.pullbackSnd_comp_pullbackEquiv`: the components of the isomorphism are the maps of
  tilts induced by the projections.
* `PreTilt.coe_untilt_pullbackEquiv_symm`: the sharp of the element of `C♭` corresponding to
  `(a, b)` is `(a♯, b♯)`.

## References

* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, §2.1.1, and the proof of
  Proposition 2.1.4, second paragraph.
-/

public section

open Ideal

variable {A B A' : Type*} [CommRing A] [CommRing B] [CommRing A']

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
  simp only [coe_untilt_pullback, RingHom.map_iterate_frobeniusEquiv_symm, h₁, h₂]

variable [IsHausdorff (span {(p : A')}) A']

/-- If `a ∈ A♭` and `b ∈ B♭` have the same image in `A'♭` and `A'` is `p`-adically separated,
then `f (a♯) = g (b♯)`: the images of the sharps of their `p ^ m`-th roots agree modulo `p`, so
`f (a♯)` and `g (b♯)` agree modulo `p ^ (m + 1)` for every `m`. -/
private theorem map_untilt_eq_of_map_eq {a : PreTilt A p} {b : PreTilt B p}
    (hab : map p f a = map p g b) : f a.untilt = g b.untilt := by
  refine sub_eq_zero.mp <| IsHausdorff.haus (I := span {(p : A')}) inferInstance _ fun m ↦ ?_
  rw [TauCeti.sModEq_span_singleton_pow_iff, sub_zero]
  have hm : (p : A') ∣ f (untilt ((frobeniusEquiv (PreTilt A p) p).symm^[m] a)) -
      g (untilt ((frobeniusEquiv (PreTilt B p) p).symm^[m] b)) := by
    rw [← mem_span_singleton, ← Ideal.Quotient.eq, ← ModP.map_mk, ← ModP.map_mk,
      ← coeff_eq_mk_untilt_iterate, ← coeff_eq_mk_untilt_iterate, ← coeff_map, ← coeff_map, hab]
  have h := dvd_sub_pow_of_dvd_sub hm m
  rw [← map_pow f, ← map_pow g, untilt_iterate_frobeniusEquiv_symm_pow,
    untilt_iterate_frobeniusEquiv_symm_pow] at h
  exact (pow_dvd_pow _ m.le_succ).trans h

/-- The comparison homomorphism is surjective: for `a ∈ A♭` and `b ∈ B♭` with the same image in
`A'♭`, the pairs of sharps of their `p`-power roots form a compatible system of `p`-th roots in the
fibre product, whose reduction modulo `p` is a preimage of `(a, b)`. -/
private theorem pullbackHom_surjective : Function.Surjective (pullbackHom p f g) := by
  rintro ⟨⟨a, b⟩, hab⟩
  -- the compatible system `((a ^ (1 / p ^ n))♯, (b ^ (1 / p ^ n))♯)ₙ` in the fibre product
  have hc (n : ℕ) : (untilt ((frobeniusEquiv (PreTilt A p) p).symm^[n] a),
      untilt ((frobeniusEquiv (PreTilt B p) p).symm^[n] b)) ∈ f.pullback g :=
    RingHom.mem_pullback_iff.mpr <| map_untilt_eq_of_map_eq p f g <| by
      simp only [RingHom.map_iterate_frobeniusEquiv_symm, RingHom.mem_pullback_iff.mp hab]
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
  refine ⟨x, Subtype.ext (Prod.ext (ext fun n ↦ ?_) (ext fun n ↦ ?_))⟩ <;>
  · rw [RingHom.coe_pullbackLift_apply, coeff_map, hx, ModP.map_mk, coeff_eq_mk_untilt_iterate]
    simp [c]

variable [IsAdicComplete (span {(p : f.pullback g)}) (f.pullback g)]

/-- **The tilt of a fibre product is the fibre product of the tilts.** For `p`-adically complete
rings `A`, `B`, a `p`-adically separated ring `A'` and ring homomorphisms `f : A →+* A'`,
`g : B →+* A'` whose fibre product `A ×_{A'} B` is `p`-adically complete, the projections induce
a ring isomorphism `(A ×_{A'} B)♭ ≃+* A♭ ×_{A'♭} B♭`. -/
noncomputable def pullbackEquiv :
    PreTilt (f.pullback g) p ≃+* (map p f).pullback (map p g) :=
  RingEquiv.ofBijective (pullbackHom p f g)
    ⟨pullbackHom_injective p f g, pullbackHom_surjective p f g⟩

variable {p f g}

/-- `PreTilt.pullbackEquiv` sends `x` to the pair of its images under the maps of tilts induced by
the two projections. -/
@[simp]
theorem coe_pullbackEquiv_apply (x : PreTilt (f.pullback g) p) :
    (pullbackEquiv p f g x : PreTilt A p × PreTilt B p) =
      (map p (f.pullbackFst g) x, map p (f.pullbackSnd g) x) := by
  rw [pullbackEquiv]
  exact RingHom.coe_pullbackLift_apply ..

/-- The first projection of `PreTilt.pullbackEquiv` is the map of tilts induced by the first
projection of the fibre product. -/
@[simp]
theorem pullbackFst_comp_pullbackEquiv :
    ((map p f).pullbackFst (map p g)).comp (pullbackEquiv p f g : _ →+* _) =
      map p (f.pullbackFst g) :=
  RingHom.ext fun x ↦ congrArg Prod.fst (coe_pullbackEquiv_apply x)

/-- The second projection of `PreTilt.pullbackEquiv` is the map of tilts induced by the second
projection of the fibre product. -/
@[simp]
theorem pullbackSnd_comp_pullbackEquiv :
    ((map p f).pullbackSnd (map p g)).comp (pullbackEquiv p f g : _ →+* _) =
      map p (f.pullbackSnd g) :=
  RingHom.ext fun x ↦ congrArg Prod.snd (coe_pullbackEquiv_apply x)

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

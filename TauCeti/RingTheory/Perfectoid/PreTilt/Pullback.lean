/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Perfectoid.PreTilt.Map
public import TauCeti.RingTheory.WittVector.MapEquiv
public import TauCeti.RingTheory.WittVector.Primitive.Basic
public import TauCeti.RingTheory.WittVector.Pullback

/-!
# Tilts and `A_inf` of pullbacks

Let `f : A →+* T` and `g : B →+* T` be ring homomorphisms and `C = A ×_T B` their pullback, the
subring `f.pullback g` of `A × B` on which `f` and `g` agree. The tilts of the two projections
`C → A` and `C → B` land in the pullback of tilts, giving a ring homomorphism
`PreTilt.toPullback p f g : C♭ →+* A♭ ×_{T♭} B♭`. It is an isomorphism as soon as `A`, `B` and `C`
are `p`-adically complete and `T` is `p`-adically Hausdorff:

* **Injectivity.** The `n`-th coordinate of `x ∈ C♭` is the reduction of `(x ^ (1 / p ^ n))♯`, and
  the sharp map is natural, so the components of this element of `C ⊆ A × B` are the sharps of the
  `p ^ n`-th roots of the images of `x` in `A♭` and `B♭`.
* **Surjectivity.** For `(u, v) ∈ A♭ ×_{T♭} B♭`, the pairs
  `((u ^ (1 / p ^ n))♯, (v ^ (1 / p ^ n))♯)` lie in `C`, because `f (u'♯) = g (v'♯)` whenever `u'`
  and `v'` have the same image in `T♭` and `T` is separated (`PreTilt.apply_untilt_eq_of_map_eq`).
  They form a compatible system of `p`-th roots, whose reductions modulo `p` define the preimage of
  `(u, v)`.

The `p`-adic completeness of `C` holds when `A` and `B` are complete, `T` is separated and the
`p`-power torsion of `T` is killed by `p` (`IsAdicComplete.pullback_span_natCast`); this is the case
for integral perfectoid `T`. Witt vectors commute with pullbacks (`WittVector.pullbackEquiv`), so
`A_inf(C) = W(C♭)` is the pullback `A_inf(A) ×_{A_inf(T)} A_inf(B)`, compatibly with Fontaine's maps
`θ`. This is the description of the tilt and of `A_inf` of a fibre product used to show that fibre
products of integral perfectoid rings along a surjection are integral perfectoid.

## Main definitions

* `PreTilt.toPullback p f g : PreTilt (f.pullback g) p →+* (map p f).pullback (map p g)`: the
  comparison map, by the tilts of the projections.
* `PreTilt.pullbackEquiv p f g`: the comparison map as a ring isomorphism `C♭ ≃+* A♭ ×_{T♭} B♭`.
* `PreTilt.wittVectorPullbackEquiv p f g`: `A_inf(C) ≃+* A_inf(A) ×_{A_inf(T)} A_inf(B)`.

## Main results

* `PreTilt.toPullback_injective`, `PreTilt.toPullback_surjective`: the comparison map is injective
  when `A`, `B` and `C` are `p`-adically complete, and surjective when `A` and `B` are and `T` is
  `p`-adically Hausdorff.
* `PreTilt.coe_untilt_pullbackEquiv_symm`: the tilt isomorphism is compatible with the sharp maps.
* `PreTilt.coe_fontaineTheta_wittVectorPullbackEquiv_symm`,
  `PreTilt.coe_fontaineTheta_wittVectorPullbackEquiv`: the `A_inf` isomorphism is compatible with
  Fontaine's maps.
* `PreTilt.mem_ker_fontaineTheta_iff_wittVectorPullbackEquiv`: an element of `A_inf(A ×_T B)` lies
  in `ker θ` exactly when both of its components do.
* `PreTilt.isDistinguished_iff_wittVectorPullbackEquiv`: an element of `A_inf(A ×_T B)` is
  distinguished exactly when both of its components are.

## References

* K. Česnavičius, P. Scholze, *Purity for flat cohomology*, §2.1.1, p. 10, and the proof of
  Proposition 2.1.4, p. 12.
-/

public section

open Ideal

variable {A B T : Type*} [CommRing A] [CommRing B] [CommRing T]

/-- The pullback `A ×_T B` is a ring in which `p` is not a unit as soon as `p` is not a unit in
`A`. -/
instance RingHom.fact_not_isUnit_natCast_pullback (p : ℕ) (f : A →+* T) (g : B →+* T)
    [Fact ¬IsUnit (p : A)] : Fact ¬IsUnit (p : f.pullback g) :=
  ⟨fun h ↦ Fact.out (p := ¬IsUnit (p : A)) (by simpa using h.map (f.pullbackFst g))⟩

namespace PreTilt

variable (p : ℕ) [Fact p.Prime] (f : A →+* T) (g : B →+* T) [Fact ¬IsUnit (p : A)]
  [Fact ¬IsUnit (p : B)] [Fact ¬IsUnit (p : T)]

/-- The comparison map `(A ×_T B)♭ →+* A♭ ×_{T♭} B♭` from the tilt of a pullback to the pullback of
the tilts, by the tilts of the two projections. -/
noncomputable def toPullback : PreTilt (f.pullback g) p →+* (map p f).pullback (map p g) :=
  ((map p (f.pullbackFst g)).prod (map p (f.pullbackSnd g))).codRestrict _ fun x ↦
    RingHom.mem_pullback.mpr <| by
      simp [← RingHom.comp_apply, ← map_comp, RingHom.pullback_comm_sq]

variable {p f g}

/-- The image of `x` under `PreTilt.toPullback` is the pair of its images under the tilts of the
two projections. -/
@[simp]
theorem coe_toPullback (x : PreTilt (f.pullback g) p) :
    (toPullback p f g x : PreTilt A p × PreTilt B p) =
      (map p (f.pullbackFst g) x, map p (f.pullbackSnd g) x) :=
  (rfl)

/-- For `p`-adically complete `A`, `B` and `A ×_T B`, the tilt of the pullback embeds in the
pullback of the tilts. -/
theorem toPullback_injective [IsAdicComplete (span {(p : A)}) A]
    [IsAdicComplete (span {(p : B)}) B]
    [IsAdicComplete (span {(p : f.pullback g)}) (f.pullback g)] :
    Function.Injective (toPullback p f g) := by
  refine (injective_iff_map_eq_zero _).mpr fun x hx ↦ ext fun n ↦ ?_
  have hx' := congr(($hx : PreTilt A p × PreTilt B p))
  simp only [coe_toPullback, ZeroMemClass.coe_zero, Prod.mk_eq_zero] at hx'
  -- the sharp of the `p ^ n`-th root of `x` has components the sharps of the `p ^ n`-th roots of
  -- the images of `x` in `A♭` and `B♭`, which vanish
  have h0 : untilt ((frobeniusEquiv (PreTilt (f.pullback g) p) p).symm^[n] x) = 0 := by
    refine Subtype.ext (Prod.ext ?_ ?_)
    · simpa [RingHom.map_iterate_frobeniusEquiv_symm, hx'.1] using
        (untilt_natural (f.pullbackFst g) ((frobeniusEquiv _ p).symm^[n] x)).symm
    · simpa [RingHom.map_iterate_frobeniusEquiv_symm, hx'.2] using
        (untilt_natural (f.pullbackSnd g) ((frobeniusEquiv _ p).symm^[n] x)).symm
  rw [coeff_eq_mk_untilt_iterate, h0, map_zero, map_zero]

/-- For `p`-adically complete `A` and `B` and `p`-adically Hausdorff `T`, every element of the
pullback of the tilts comes from the tilt of the pullback. -/
theorem toPullback_surjective [IsAdicComplete (span {(p : A)}) A]
    [IsAdicComplete (span {(p : B)}) B] [IsHausdorff (span {(p : T)}) T] :
    Function.Surjective (toPullback p f g) := by
  rintro ⟨⟨u, v⟩, huv⟩
  have huv' : map p f u = map p g v := RingHom.mem_pullback.mp huv
  -- the sharps of the `p ^ n`-th roots of `u` and `v` form a compatible system in the pullback
  let c (n : ℕ) : f.pullback g :=
    ⟨(untilt ((frobeniusEquiv _ p).symm^[n] u), untilt ((frobeniusEquiv _ p).symm^[n] v)),
      RingHom.mem_pullback.mpr <| apply_untilt_eq_of_map_eq (by
        rw [RingHom.map_iterate_frobeniusEquiv_symm, RingHom.map_iterate_frobeniusEquiv_symm,
          huv'])⟩
  have hc (n : ℕ) : c (n + 1) ^ p = c n :=
    Subtype.ext (Prod.ext (untilt_iterate_frobeniusEquiv_symm_succ_pow u n)
      (untilt_iterate_frobeniusEquiv_symm_succ_pow v n))
  let x : PreTilt (f.pullback g) p :=
    equivPerfection.symm ⟨fun n ↦ Ideal.Quotient.mk _ (c n), fun n ↦ by rw [← map_pow, hc]⟩
  have hx (n : ℕ) : coeff n x = Ideal.Quotient.mk _ (c n) :=
    (coeff_equivPerfection_symm _ n).trans (Perfection.coeff_mk _ _ n)
  refine ⟨x, Subtype.ext (Prod.ext (ext fun n ↦ ?_) (ext fun n ↦ ?_))⟩
  all_goals
    rw [coe_toPullback, coeff_map, hx, ModP.map_mk, coeff_eq_mk_untilt_iterate]
    simp [c]

variable (p f g)

/-- **The tilt of a pullback is the pullback of the tilts**: for `p`-adically complete `A`, `B` and
`A ×_T B` and `p`-adically Hausdorff `T`, the tilts of the projections induce a ring isomorphism
`(A ×_T B)♭ ≃+* A♭ ×_{T♭} B♭`. -/
noncomputable def pullbackEquiv [IsAdicComplete (span {(p : A)}) A]
    [IsAdicComplete (span {(p : B)}) B]
    [IsAdicComplete (span {(p : f.pullback g)}) (f.pullback g)] [IsHausdorff (span {(p : T)}) T] :
    PreTilt (f.pullback g) p ≃+* (map p f).pullback (map p g) :=
  RingEquiv.ofBijective (toPullback p f g) ⟨toPullback_injective, toPullback_surjective⟩

variable [IsAdicComplete (span {(p : A)}) A] [IsAdicComplete (span {(p : B)}) B]
  [IsAdicComplete (span {(p : f.pullback g)}) (f.pullback g)] [IsHausdorff (span {(p : T)}) T]

variable {p f g}

@[simp]
theorem pullbackEquiv_apply (x : PreTilt (f.pullback g) p) :
    pullbackEquiv p f g x = toPullback p f g x :=
  (rfl)

/-- The sharp of the element of `(A ×_T B)♭` corresponding to a pair `y` of the pullback of the
tilts is the pair of sharps. -/
@[simp]
theorem coe_untilt_pullbackEquiv_symm (y : (map p f).pullback (map p g)) :
    (((pullbackEquiv p f g).symm y).untilt : A × B) =
      ((y : PreTilt A p × PreTilt B p).1.untilt, (y : PreTilt A p × PreTilt B p).2.untilt) := by
  obtain ⟨x, rfl⟩ := (pullbackEquiv p f g).surjective y
  rw [RingEquiv.symm_apply_apply, pullbackEquiv_apply, coe_toPullback, untilt_natural,
    untilt_natural]
  simp

variable (p f g)

/-- **`A_inf` of a pullback is the pullback of the `A_inf`**:
`W((A ×_T B)♭) ≃+* W(A♭) ×_{W(T♭)} W(B♭)`, the Witt vectors of `PreTilt.pullbackEquiv`
(`WittVector.mapEquiv`) followed by `WittVector.pullbackEquiv`. -/
noncomputable def wittVectorPullbackEquiv :
    WittVector p (PreTilt (f.pullback g) p) ≃+*
      (WittVector.map (p := p) (map p f)).pullback (WittVector.map (map p g)) :=
  (WittVector.mapEquiv (pullbackEquiv p f g)).trans (WittVector.pullbackEquiv p (map p f) (map p g))

variable {p f g}

/-- The image of `w` under `PreTilt.wittVectorPullbackEquiv` is the pair of its images under the
Witt vectors of the tilts of the two projections. -/
@[simp]
theorem coe_wittVectorPullbackEquiv (w : WittVector p (PreTilt (f.pullback g) p)) :
    (wittVectorPullbackEquiv p f g w : WittVector p (PreTilt A p) × WittVector p (PreTilt B p)) =
      (WittVector.map (map p (f.pullbackFst g)) w, WittVector.map (map p (f.pullbackSnd g)) w) :=
  Prod.ext (WittVector.ext fun n ↦ by simp [wittVectorPullbackEquiv, WittVector.map_coeff])
    (WittVector.ext fun n ↦ by simp [wittVectorPullbackEquiv, WittVector.map_coeff])

/-- An element of `A_inf(A ×_T B)` is distinguished exactly when both of its components in
`A_inf(A)` and `A_inf(B)` are. -/
theorem isDistinguished_iff_wittVectorPullbackEquiv
    {ξ : WittVector p (PreTilt (f.pullback g) p)} :
    ξ.IsDistinguished ↔
      (wittVectorPullbackEquiv p f g ξ :
        WittVector p (PreTilt A p) × WittVector p (PreTilt B p)).1.IsDistinguished ∧
      (wittVectorPullbackEquiv p f g ξ :
        WittVector p (PreTilt A p) × WittVector p (PreTilt B p)).2.IsDistinguished := by
  rw [coe_wittVectorPullbackEquiv]
  simp only [WittVector.isDistinguished_iff, WittVector.map_coeff]
  rw [← isUnit_map_iff (pullbackEquiv p f g),
    ← Subtype.coe_eta (pullbackEquiv p f g _) (pullbackEquiv p f g _).property,
    RingHom.isUnit_pullback_mk_iff]
  simp

/-- **Fontaine's map of a pullback is the pair of Fontaine's maps**: under
`A_inf(A ×_T B) ≃+* A_inf(A) ×_{A_inf(T)} A_inf(B)`, `θ` of the pullback is computed
componentwise. -/
@[simp]
theorem coe_fontaineTheta_wittVectorPullbackEquiv_symm
    (v : (WittVector.map (p := p) (map p f)).pullback (WittVector.map (map p g))) :
    (WittVector.fontaineTheta (f.pullback g) p ((wittVectorPullbackEquiv p f g).symm v) : A × B) =
      (WittVector.fontaineTheta A p (v : WittVector p (PreTilt A p) × WittVector p (PreTilt B p)).1,
        WittVector.fontaineTheta B p
          (v : WittVector p (PreTilt A p) × WittVector p (PreTilt B p)).2) := by
  obtain ⟨w, rfl⟩ := (wittVectorPullbackEquiv p f g).surjective v
  simp only [RingEquiv.symm_apply_apply, coe_wittVectorPullbackEquiv, WittVector.theta_natural]
  simp

/-- Fontaine's map of `A ×_T B` is computed componentwise on the image of `w` in
`A_inf(A) ×_{A_inf(T)} A_inf(B)`. -/
theorem coe_fontaineTheta_wittVectorPullbackEquiv (w : WittVector p (PreTilt (f.pullback g) p)) :
    (WittVector.fontaineTheta (f.pullback g) p w : A × B) =
      (WittVector.fontaineTheta A p (wittVectorPullbackEquiv p f g w :
          WittVector p (PreTilt A p) × WittVector p (PreTilt B p)).1,
        WittVector.fontaineTheta B p (wittVectorPullbackEquiv p f g w :
          WittVector p (PreTilt A p) × WittVector p (PreTilt B p)).2) := by
  simp

/-- An element of `A_inf(A ×_T B)` lies in the kernel of Fontaine's map exactly when both of its
components in `A_inf(A)` and `A_inf(B)` do. -/
theorem mem_ker_fontaineTheta_iff_wittVectorPullbackEquiv
    {w : WittVector p (PreTilt (f.pullback g) p)} :
    w ∈ RingHom.ker (WittVector.fontaineTheta (f.pullback g) p) ↔
      (wittVectorPullbackEquiv p f g w :
        WittVector p (PreTilt A p) × WittVector p (PreTilt B p)).1 ∈
          RingHom.ker (WittVector.fontaineTheta A p) ∧
      (wittVectorPullbackEquiv p f g w :
        WittVector p (PreTilt A p) × WittVector p (PreTilt B p)).2 ∈
          RingHom.ker (WittVector.fontaineTheta B p) := by
  rw [RingHom.mem_ker, ← ZeroMemClass.coe_eq_zero, coe_fontaineTheta_wittVectorPullbackEquiv,
    Prod.mk_eq_zero, RingHom.mem_ker, RingHom.mem_ker]

end PreTilt

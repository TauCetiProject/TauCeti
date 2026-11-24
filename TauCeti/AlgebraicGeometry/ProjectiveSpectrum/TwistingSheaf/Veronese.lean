/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Functor
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.Veronese

/-!
# Twisting sheaves and Veronese subalgebras

Let `A = ⨁ₙ 𝒜 n` be an `ℕ`-graded commutative `R`-algebra, `d ≠ 0`, and let
`A^{(d)} = ⨁ₖ 𝒜 (d k)` be its Veronese subalgebra (`TauCeti.GradedAlgebra.veronese`),
with grading `TauCeti.GradedAlgebra.veroneseGrading`.
The inverse of the isomorphism `AlgebraicGeometry.Proj.veroneseIso : Proj A^{(d)} ≅ Proj A`
sends a point `q` of `Proj A` to its contraction `q ∩ A^{(d)}`
(`AlgebraicGeometry.Proj.toIdeal_asHomogeneousIdeal_veroneseIso_inv`).

Over it, a local fraction `r / s` of degree `n` for `A^{(d)}` (so `r ∈ 𝒜 (d j)`, `s ∈ 𝒜 (d i)` and
`j = i + n`) is a local fraction of degree `d n` for `A`. We construct the induced pullback of
sections of twisting sheaves

`Γ(U, 𝒪_{Proj A^{(d)}}(n)) → Γ(V, 𝒪_{Proj A}(d n))`

for `V` contained in the preimage of `U` (`AlgebraicGeometry.Proj.twistingSheaf.comapVeronese`):
it applies the maps of localizations `A^{(d)}_{q ∩ A^{(d)}} → A_q`
(`Localization.localRingHom`) pointwise. This is the map underlying the
identification of `𝒪(n)` on `Proj A^{(d)}` with `𝒪(d n)` on `Proj A`
(Stacks, Lemma 27.11.8 (0B5J)). Let `g ∈ A^{(d)}` be homogeneous of positive degree `e` in the
grading of `A^{(d)}`, so of degree `d e` in `A`. For `U = D₊(g) ⊆ Proj A^{(d)}` and `V` its full
preimage `D₊(g) ⊆ Proj A`, the pullback is bijective
(`AlgebraicGeometry.Proj.twistingSheaf.bijective_comapVeronese_basicOpen`): both sides are the
fractions `r / gᵏ` with `r ∈ 𝒜 (d (k e + n))`.

The construction uses the pointwise pullback of localization-valued functions along a continuous
map and a ring homomorphism contracting prime ideals
(`AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.comapFun`). Preservation of local fractions
with the specified degree change is proved by
`AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.isLocallyFraction_comapFun`. Together these
also give the pullback along `Proj.map` (`AlgebraicGeometry.Proj.twistingSheaf.comap`); here the
inclusion `A^{(d)} → A` multiplies degrees by `d`.

## Main definitions

* `AlgebraicGeometry.Proj.twistingSheaf.comapVeronese`: the pullback of sections
  `Γ(U, 𝒪_{Proj A^{(d)}}(n)) → Γ(V, 𝒪_{Proj A}(d n))`.

## Main results

* `AlgebraicGeometry.Proj.twistingSheaf.comapVeronese_const`: the pullback of the fraction `r / s`
  is the fraction `r / s`.
* `AlgebraicGeometry.Proj.twistingSheaf.comapVeronese_toTwistingSheaf`: the section `r / 1` of
  degree `j` over `A^{(d)}` pulls back to the section `r / 1` of degree `d j` over `A`.
* `AlgebraicGeometry.Proj.twistingSheaf.bijective_comapVeronese_basicOpen`: for `g ∈ A^{(d)}`
  homogeneous of positive degree, the pullback from `D₊(g) ⊆ Proj A^{(d)}` to its full preimage
  `D₊(g) ⊆ Proj A` is bijective.

## References

* [Stacks, Lemma 27.11.8 (0B5J)](https://stacks.math.columbia.edu/tag/0B5J)
-/

public section

noncomputable section

namespace AlgebraicGeometry

open CategoryTheory TopologicalSpace TauCeti.GradedAlgebra ProjectiveSpectrum.TwistingSheaf

universe u

variable {R : Type*} {A : Type u} [CommRing R] [CommRing A] [Algebra R A]
  {𝒜 : ℕ → Submodule R A} [GradedAlgebra 𝒜] {d : ℕ} [NeZero d]

namespace Proj.twistingSheaf

variable {n : ℤ} {U : (Proj (veroneseGrading 𝒜 d)).Opens} {V : (Proj 𝒜).Opens}
  (hUV : V ≤ (veroneseIso 𝒜 d).inv ⁻¹ᵁ U)

/-- **Pullback of sections of twisting sheaves along the Veronese contraction**: for `V ⊆ Proj A`
contained in the preimage of `U ⊆ Proj A^{(d)}` under `Proj A ≅ Proj A^{(d)}`, the map
`Γ(U, 𝒪_{Proj A^{(d)}}(n)) → Γ(V, 𝒪_{Proj A}(d n))` applying the maps of localizations
`A^{(d)}_{q ∩ A^{(d)}} → A_q` pointwise. -/
def comapVeronese :
    Γ(twistingSheaf (veroneseGrading 𝒜 d) n, U) →+ Γ(twistingSheaf 𝒜 (d * n), V) where
  toFun s := ⟨comapFun (veroneseIso 𝒜 d).inv.base.hom (veronese 𝒜 d).val.toRingHom
      (toIdeal_asHomogeneousIdeal_veroneseIso_inv 𝒜 d) hUV s.val,
    isLocallyFraction_comapFun (δ := (d * ·)) (fun _ _ ↦ mem_veroneseGrading.mp)
      (fun i j h ↦ by push_cast; rw [h]; ring) s.property⟩
  map_zero' := ext fun _ ↦ (comapFun_apply ..).trans (map_zero _)
  -- Section addition reduces pointwise here. `add_apply` does not unify with the codomain's
  -- inferred addition through the unexposed localization addition instance.
  map_add' _ _ := ext fun _ ↦ (comapFun_apply ..).trans
    ((map_add _ _ _).trans (congrArg₂ (· + ·) (comapFun_apply ..).symm (comapFun_apply ..).symm))

/-- The value of a pulled-back section at `q` is the image of its value at `q ∩ A^{(d)}`. -/
@[simp]
theorem comapVeronese_apply (s : Γ(twistingSheaf (veroneseGrading 𝒜 d) n, U)) (q : V) :
    letI := ProjectiveSpectrum.isPrime ((veroneseIso 𝒜 d).inv q.val)
    letI := ProjectiveSpectrum.isPrime q.val
    (comapVeronese hUV s).val q =
      Localization.localRingHom _ _ (veronese 𝒜 d).val.toRingHom
        (toIdeal_asHomogeneousIdeal_veroneseIso_inv 𝒜 d q.val)
        (s.val (⟨(veroneseIso 𝒜 d).inv q.val, hUV q.property⟩ : U)) :=
  comapFun_apply ..

/-- The pullback along the Veronese contraction commutes with restriction. -/
@[simp]
theorem res_comapVeronese {V' : (Proj 𝒜).Opens} (i : V' ⟶ V)
    (s : Γ(twistingSheaf (veroneseGrading 𝒜 d) n, U)) :
    (twistingSheaf 𝒜 (d * n)).presheaf.map i.op (comapVeronese hUV s) =
      comapVeronese (i.le.trans hUV) s :=
  -- after the rewrites the two sides evaluate `s` at the same point, given by different proofs
  ext fun _ ↦ by rw [res_apply, comapVeronese_apply, comapVeronese_apply]; rfl

/-- Pulling back the restriction of a section along the Veronese contraction is pulling back the
section. -/
@[simp]
theorem comapVeronese_res {U' : (Proj (veroneseGrading 𝒜 d)).Opens} (i : U' ⟶ U)
    (hU'V : V ≤ (veroneseIso 𝒜 d).inv ⁻¹ᵁ U')
    (s : Γ(twistingSheaf (veroneseGrading 𝒜 d) n, U)) :
    comapVeronese hU'V ((twistingSheaf (veroneseGrading 𝒜 d) n).presheaf.map i.op s) =
      comapVeronese (hU'V.trans (Scheme.Hom.preimage_mono _ i.le)) s :=
  -- after the rewrites the two sides evaluate `s` at the same point, given by different proofs
  ext fun _ ↦ by rw [comapVeronese_apply, comapVeronese_apply, res_apply]; rfl

/-- The pullback of the fraction `r / s` of degree `n` over `A^{(d)}` is the same fraction, of
degree `d n`, over `A`. -/
@[simp]
theorem comapVeronese_const {i j : ℕ} (h : (j : ℤ) = i + n) (r s : veronese 𝒜 d)
    (hr : r ∈ veroneseGrading 𝒜 d j) (hs : s ∈ veroneseGrading 𝒜 d i)
    (hU : U ≤ basicOpen _ s) :
    comapVeronese hUV (const h r s hr hs U hU) =
      const (i := d * i) (j := d * j) (by push_cast; rw [h]; ring) (r : A) (s : A)
        (mem_veroneseGrading.mp hr) (mem_veroneseGrading.mp hs) V
        ((hUV.trans (Scheme.Hom.preimage_mono _ hU)).trans
          (veroneseIso_inv_preimage_basicOpen 𝒜 d s).le) :=
  ext <| comapFun_const (toIdeal_asHomogeneousIdeal_veroneseIso_inv 𝒜 d) hUV (δ := (d * ·))
    (fun _ _ ↦ mem_veroneseGrading.mp) (fun i j h ↦ by push_cast; rw [h]; ring) h r s hr hs hU

/-- The section `r / 1` induced by an element `r` of degree `j` of `A^{(d)}` pulls back to the
section `r / 1` induced by `r` as an element of degree `d j` of `A`. -/
@[simp]
theorem comapVeronese_toTwistingSheaf {j : ℕ} (h : (j : ℤ) = n) (r : veroneseGrading 𝒜 d j) :
    comapVeronese hUV (toTwistingSheaf (veroneseGrading 𝒜 d) h U r) =
      toTwistingSheaf 𝒜 (j := d * j) (by rw [← h]; push_cast; rfl) V
        ⟨r, mem_veroneseGrading.mp r.property⟩ := by
  rw [toTwistingSheaf_eq_const, comapVeronese_const, toTwistingSheaf_eq_const]
  exact const_ext (by simp)

/-- **Pullback along the Veronese contraction is bijective on standard opens.** For `g ∈ A^{(d)}`
homogeneous of positive degree, the preimage of `D₊(g) ⊆ Proj A^{(d)}` is `D₊(g) ⊆ Proj A`
(`AlgebraicGeometry.Proj.veroneseIso_inv_preimage_basicOpen`), and the pullback
`Γ(D₊(g), 𝒪_{Proj A^{(d)}}(n)) → Γ(D₊(g), 𝒪_{Proj A}(d n))` is bijective: both sides are the
fractions `r / gᵏ` with `r ∈ 𝒜 (d (k e + n))`, where `e > 0` is the degree of `g` in the grading of
`A^{(d)}`, so that `g ∈ 𝒜 (d e)`. -/
theorem bijective_comapVeronese_basicOpen {e : ℕ} {g : veronese 𝒜 d}
    (hg : g ∈ veroneseGrading 𝒜 d e) (he : 0 < e) :
    Function.Bijective (comapVeronese (n := n) (U := basicOpen (veroneseGrading 𝒜 d) g)
      (V := basicOpen 𝒜 (g : A)) (veroneseIso_inv_preimage_basicOpen 𝒜 d g).ge) := by
  have hgA : (g : A) ∈ 𝒜 (d * e) := mem_veroneseGrading.mp hg
  have hde : 0 < d * e := Nat.mul_pos (NeZero.pos d) he
  refine ⟨(injective_iff_map_eq_zero _).2 fun s hs ↦ ?_, fun t ↦ ?_⟩
  · -- `s = r / gᵏ` over `A^{(d)}` vanishes over `A`, so a power of `g` kills `r` in `A^{(d)}`
    obtain ⟨k, j, h, r, hr, rfl⟩ := exists_eq_const_basicOpen (𝒜 := veroneseGrading 𝒜 d) hg he s
    obtain ⟨N, hN⟩ := (const_eq_zero_iff (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hde hgA) ..).1
      ((comapVeronese_const ..).symm.trans hs)
    exact (const_eq_zero_iff (HomogeneousIdeal.mem_irrelevant_of_mem _ he hg) ..).2
      ⟨N, Subtype.ext (by simpa using hN)⟩
  · obtain ⟨k, j, h, r, hr, rfl⟩ := exists_eq_const_basicOpen (𝒜 := 𝒜) hgA hde t
    -- the numerator has degree `j = d (k e + n)`, so it lies in `A^{(d)}`
    have hnn : (0 : ℤ) ≤ k * e + n := by
      have hj := Int.natCast_nonneg j
      push_cast at h
      rw [h, mul_left_comm (k : ℤ), ← mul_add] at hj
      exact nonneg_of_mul_nonneg_right hj (by exact_mod_cast NeZero.pos d)
    have hj' : ((k * e + n).toNat : ℤ) = k * e + n := Int.toNat_of_nonneg hnn
    have hjd' : (j : ℤ) = d * (k * e + n).toNat := by rw [h, hj']; push_cast; ring
    have hjd : j = d * (k * e + n).toNat := by exact_mod_cast hjd'
    have hr' : r ∈ 𝒜 (d * (k * e + n).toNat) := hjd ▸ hr
    have hgk : g ^ k ∈ veroneseGrading 𝒜 d (k * e) := by
      simpa [mul_comm] using SetLike.pow_mem_graded k hg
    refine ⟨const (i := k * e) (j := (k * e + n).toNat) (by rw [hj']; push_cast; ring)
      ⟨r, mem_veronese_of_mem hr'⟩ (g ^ k) (mem_veroneseGrading.mpr hr') hgk _
      fun x hx hgk ↦ hx (x.isPrime.mem_of_pow_mem k hgk), ?_⟩
    exact (comapVeronese_const ..).trans (const_ext (by simp [mul_comm]))

end Proj.twistingSheaf

end AlgebraicGeometry

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic

/-!
# Sections of twisting sheaves over standard opens

Let `f` be a homogeneous element of positive degree `d` of an `ℕ`-graded commutative ring `A`.
This file computes the sections of the twisting sheaf `𝒪(n)` over the standard open `D₊(f)`:
every section is a fraction `r / fᵏ` with `r` homogeneous of degree `k * d + n`
(`AlgebraicGeometry.Proj.twistingSheaf.exists_eq_const_basicOpen`), and two fractions agree on
`D₊(f)` exactly when they agree in the localization `A_f`
(`AlgebraicGeometry.Proj.twistingSheaf.const_eq_const_iff`). Together these identify
`Γ(D₊(f), 𝒪(n))` with the degree-`n` part of the `ℤ`-graded ring `A_f`. As `D₊(f) ∩ D₊(g)` is the
standard open `D₊(f g)`, they are the key input for describing the restriction maps between
standard opens as localizations, and hence for proving that `𝒪(n)` is quasi-coherent.

For `n = 0`, Mathlib obtains `Γ(D₊(f), 𝒪) = A_{(f)}` from the isomorphism
`D₊(f) ≅ Spec A_{(f)}` (`AlgebraicGeometry.Proj.basicOpenIsoSpec`). Here we argue directly with
local fractions, which works for every twist `n`, including those not divisible by `d`. The
proofs follow Mathlib's computation of the sections of the structure sheaf of `Spec` over basic
opens (`AlgebraicGeometry.StructureSheaf.toBasicOpenₗ_injective`,
`AlgebraicGeometry.StructureSheaf.exists_le_iSup_basicOpen_and_smul_eq_smul_and_eq_const` and
`AlgebraicGeometry.StructureSheaf.toBasicOpenₗ_surjective` in
`Mathlib/AlgebraicGeometry/StructureSheaf.lean`): the fractions describing a section near the
points of the quasi-compact open `D₊(f)` are brought to a common form over a finite subcover, and
are then glued by `ProjectiveSpectrum.exists_mul_eq_pow_mul`, which writes a power of `f` as a
combination of their denominators through the homogeneous Nullstellensatz.

## Main results

* `AlgebraicGeometry.Proj.twistingSheaf.const_eq_zero_iff`: a fraction `r / s` vanishes on a
  standard open `D₊(g)` iff `r` is killed by a power of `g`.
* `AlgebraicGeometry.Proj.twistingSheaf.const_eq_const_iff`: two fractions agree on `D₊(g)` iff
  they agree in `A_g`.
* `AlgebraicGeometry.Proj.twistingSheaf.exists_eq_const_basicOpen`: every section of `𝒪(n)` over
  `D₊(f)` is a fraction `r / fᵏ`.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.11.
* [Stacks, Lemma 27.10.3 (01MM)](https://stacks.math.columbia.edu/tag/01MM)
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace

namespace AlgebraicGeometry.Proj.twistingSheaf

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜] {n : ℤ} {U : (Proj 𝒜).Opens}

variable {g : A}

/-- **Fractions vanishing on a standard open.** For `g` in the irrelevant ideal, for instance
homogeneous of positive degree, the section `r / s` of `𝒪(n)` vanishes on `D₊(g)` iff `r` is
killed by a power of `g`, that is iff `r / s` vanishes in the localization `A_g`. -/
theorem const_eq_zero_iff (hg : g ∈ HomogeneousIdeal.irrelevant 𝒜) {i j : ℕ}
    (h : (j : ℤ) = i + n) {r s : A} (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i)
    (hU : basicOpen 𝒜 g ≤ basicOpen 𝒜 s) :
    const h r s hr hs _ hU = 0 ↔ ∃ N, g ^ N * r = 0 := by
  refine ⟨fun h0 ↦ ProjectiveSpectrum.exists_pow_mul_eq_zero hg hr fun x hx ↦ ?_,
    fun ⟨N, hN⟩ ↦ ext fun x ↦ ?_⟩
  · have e := (const_apply ..).symm.trans (congr($h0.1 ⟨x, hx⟩).trans (zero_apply _))
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff] at e
    obtain ⟨⟨c, hc⟩, hcr⟩ := e
    exact ⟨c, hc, hcr⟩
  · refine (const_apply ..).trans (Eq.trans ?_ (zero_apply x).symm)
    rw [Localization.mk_eq_mk'_apply, IsLocalization.mk'_eq_zero_iff]
    exact ⟨⟨g ^ N, fun hgN ↦ x.2 (x.1.isPrime.mem_of_pow_mem N hgN)⟩, hN⟩

/-- **Equality of fractions on a standard open.** For `g` in the irrelevant ideal, for instance
homogeneous of positive degree, the sections `r / s` and `r' / s'` of `𝒪(n)` agree on `D₊(g)` iff
`s' * r - s * r'` is killed by a power of `g`, that is iff `r / s = r' / s'` in the localization
`A_g`. -/
theorem const_eq_const_iff (hg : g ∈ HomogeneousIdeal.irrelevant 𝒜) {i j i' j' : ℕ}
    (h : (j : ℤ) = i + n) (h' : (j' : ℤ) = i' + n) {r s r' s' : A} (hr : r ∈ 𝒜 j)
    (hs : s ∈ 𝒜 i) (hr' : r' ∈ 𝒜 j') (hs' : s' ∈ 𝒜 i') (hU : basicOpen 𝒜 g ≤ basicOpen 𝒜 s)
    (hU' : basicOpen 𝒜 g ≤ basicOpen 𝒜 s') :
    const h r s hr hs _ hU = const h' r' s' hr' hs' _ hU' ↔ ∃ N, g ^ N * (s' * r - s * r') = 0 := by
  rw [← sub_eq_zero, const_sub_const, const_eq_zero_iff hg]

/-- **Sections of `𝒪(n)` over a standard open.** For `f` homogeneous of positive degree `d`,
every section of `𝒪(n)` over `D₊(f)` is a fraction `r / fᵏ` with `r` homogeneous of degree
`k * d + n`. -/
theorem exists_eq_const_basicOpen {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (s : Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 f)) :
    ∃ (k j : ℕ) (h : (j : ℤ) = (k * d : ℕ) + n) (r : A) (hr : r ∈ 𝒜 j),
      s = const h r (f ^ k) hr (by simpa [mul_comm] using SetLike.pow_mem_graded k hf)
        (basicOpen 𝒜 f) (fun x hx ↦ fun hfk ↦ hx (x.isPrime.mem_of_pow_mem k hfk)) := by
  -- near each point `x` of `D₊(f)`, the section `s` is a fraction `r x / g x` on `D₊(g x)`
  choose i j h r g hr hg iU hi hxg H using
    fun x : basicOpen 𝒜 f ↦ locally_const_basicOpen s x.1 x.2
  -- on `D₊(g x * g y)`, the fractions `r x / g x` and `r y / g y` agree
  have hN (x y : basicOpen 𝒜 f) : ∃ N, (g x * g y) ^ N * (g y * r x - g x * r y) = 0 := by
    have hle := (basicOpen_mul 𝒜 (g x) (g y)).le
    have e : (twistingSheaf 𝒜 n).presheaf.map (homOfLE (hle.trans inf_le_left)).op
        ((twistingSheaf 𝒜 n).presheaf.map (iU x).op s) =
        (twistingSheaf 𝒜 n).presheaf.map (homOfLE (hle.trans inf_le_right)).op
          ((twistingSheaf 𝒜 n).presheaf.map (iU y).op s) :=
      ext fun _ ↦ rfl
    rwa [H x, H y, res_const, res_const, const_eq_const_iff
      (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 (by have := hi x; omega)
        (SetLike.mul_mem_graded (hg x) (hg y)))] at e
  choose N hN using hN
  -- finitely many `D₊(g x)` cover `D₊(f)`; over them, normalize to a common exponent `M`
  obtain ⟨t, ht⟩ := (isAffineOpen_basicOpen 𝒜 f hf hd).isCompact.elim_finite_subcover
    (fun x ↦ (basicOpen 𝒜 (g x) : Set (Proj 𝒜))) (fun _ ↦ (basicOpen 𝒜 _).2)
    (fun x hx ↦ Set.mem_iUnion_of_mem ⟨x, hx⟩ (hxg _))
  have hcover (y : basicOpen 𝒜 f) : ∃ x : t, y.1 ∈ basicOpen 𝒜 (g x) := by
    obtain ⟨x, hxt, hyx⟩ := Set.mem_iUnion₂.1 (ht y.2)
    exact ⟨⟨x, hxt⟩, hyx⟩
  let M := (t ×ˢ t).sup fun p ↦ N p.1 p.2
  have hnorm (x z : t) :
      g x ^ (M + 1) * (g z ^ M * r z) = g z ^ (M + 1) * (g x ^ M * r x) := by
    obtain ⟨c, hc⟩ := Nat.exists_eq_add_of_le
      ((t ×ˢ t).le_sup (f := fun p ↦ N p.1 p.2) (b := ⟨z, x⟩) (by simp))
    rw [show M = N z x + c from hc]
    linear_combination (g z * g x) ^ c * hN z x
  -- the normalized fractions `(g x ^ M * r x) / g x ^ (M + 1)` glue to a fraction `R / fᵏ`
  obtain ⟨k, J, hJ, R, hR, hgR⟩ := ProjectiveSpectrum.exists_mul_eq_pow_mul (n := n) hf hd (ι := t)
    (i := fun x ↦ (M + 1) * i x) (j := fun x ↦ M * i x + j x)
    (fun x ↦ by push_cast; rw [h x]; ring)
    (fun x ↦ by simpa using SetLike.mul_mem_graded (SetLike.pow_mem_graded M (hg x)) (hr x))
    (fun x ↦ by simpa using SetLike.pow_mem_graded (M + 1) (hg x))
    (fun y hfy ↦ (hcover ⟨y, hfy⟩).imp fun x hx hgx ↦ hx (y.isPrime.mem_of_pow_mem _ hgx))
    hnorm
  refine ⟨k, J, hJ, R, hR, ext fun y ↦ ?_⟩
  obtain ⟨x, hyx⟩ := hcover y
  -- both values are fractions in the localization at `y`, by `res_apply` and `const_apply`
  have e := res_apply (iU x) s ⟨y.1, hyx⟩
  rw [H x, const_apply] at e
  refine e.symm.trans (Eq.trans ?_ (const_apply hJ R (f ^ k) hR _ _ y).symm)
  refine Localization.mk_eq_mk_iff.2 (Localization.r_iff_exists.2
    ⟨⟨g x ^ M, fun hgM ↦ hyx (y.1.isPrime.mem_of_pow_mem M hgM)⟩, ?_⟩)
  linear_combination (hgR x).symm

end AlgebraicGeometry.Proj.twistingSheaf

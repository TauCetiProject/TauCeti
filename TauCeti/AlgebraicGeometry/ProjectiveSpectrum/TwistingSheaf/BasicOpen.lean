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
standard open `D₊(f g)`, they also describe the restriction maps between standard opens as
localizations; this is what makes `𝒪(n)` quasi-coherent.

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

* `AlgebraicGeometry.Proj.twistingSheaf.const_sub_const`: the difference of two fractions.
* `AlgebraicGeometry.Proj.twistingSheaf.const_eq_zero_iff`: a fraction `r / s` vanishes on a
  standard open `D₊(g)` iff `r` is killed by a power of `g`.
* `AlgebraicGeometry.Proj.twistingSheaf.const_eq_const_iff`: two fractions agree on `D₊(g)` iff
  they agree in `A_g`.
* `AlgebraicGeometry.Proj.twistingSheaf.locally_const_basicOpen`: every section of `𝒪(n)` is,
  near each point, a fraction `r / g` on a standard open `D₊(g)` with `g` of positive degree.
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

/-- The difference of the sections `r / s` and `r' / s'` is `(s' * r - s * r') / (s * s')`. -/
theorem const_sub_const {i j i' j' : ℕ} (h : (j : ℤ) = i + n) (h' : (j' : ℤ) = i' + n)
    {r s r' s' : A} (hr : r ∈ 𝒜 j) (hs : s ∈ 𝒜 i) (hr' : r' ∈ 𝒜 j') (hs' : s' ∈ 𝒜 i')
    (hU : U ≤ basicOpen 𝒜 s) (hU' : U ≤ basicOpen 𝒜 s') :
    const h r s hr hs U hU - const h' r' s' hr' hs' U hU' =
      const (i := i + i') (j := i' + j) (by push_cast; omega) (s' * r - s * r') (s * s')
        (sub_mem (SetLike.mul_mem_graded hs' hr)
          (by convert SetLike.mul_mem_graded hs hr' using 2; omega))
        (SetLike.mul_mem_graded hs hs') U
        (fun x hx ↦ by simpa [basicOpen_mul] using And.intro (hU hx) (hU' hx)) :=
  ext fun _ ↦ Localization.sub_mk ..

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
  · obtain ⟨⟨c, hc⟩, hcr⟩ := (IsLocalization.mk'_eq_zero_iff _ _).1
      ((Localization.mk_eq_mk'_apply _ _).symm.trans congr($h0.1 ⟨x, hx⟩))
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

/-- Every section of `𝒪(n)` is, near each point `x`, a fraction `r / g` on a standard open
`D₊(g)` containing `x`, with `g` homogeneous of positive degree. -/
theorem locally_const_basicOpen (s : Γ(twistingSheaf 𝒜 n, U)) (x : Proj 𝒜) (hx : x ∈ U) :
    ∃ (i j : ℕ) (h : (j : ℤ) = i + n) (r g : A) (hr : r ∈ 𝒜 j) (hg : g ∈ 𝒜 i)
      (iU : basicOpen 𝒜 g ⟶ U), 0 < i ∧ x ∈ basicOpen 𝒜 g ∧
        (twistingSheaf 𝒜 n).presheaf.map iU.op s = const h r g hr hg _ le_rfl := by
  obtain ⟨V, hxV, iVU, i, j, h, r, t, hr, ht, hV, hs⟩ := exists_const s x hx
  -- a standard open `D₊(a) ∋ x` inside `V`, and a homogeneous component `aₘ` of `a` not in `x`
  obtain ⟨_, ⟨a, rfl⟩, hxa, haV⟩ := Opens.isBasis_iff_nbhd.1 (isBasis_basicOpen 𝒜) hxV
  obtain ⟨m, hm⟩ : ∃ m, x ∈ basicOpen 𝒜 (GradedRing.proj 𝒜 m a) := by
    simpa [basicOpen_eq_iSup_proj 𝒜 a] using hxa
  -- a homogeneous element `p` of positive degree not in `x`
  obtain ⟨l, hl, p, hp, hpx⟩ := x.exists_le_mem_notMem 1
  have hg : t * GradedRing.proj 𝒜 m a * p ∈ 𝒜 (i + m + l) :=
    SetLike.mul_mem_graded (SetLike.mul_mem_graded ht (SetLike.coe_mem _)) hp
  have hgV : basicOpen 𝒜 (t * GradedRing.proj 𝒜 m a * p) ≤ V := fun y hy ↦ by
    simp only [basicOpen_mul, Opens.mem_inf] at hy
    exact haV ((basicOpen_eq_iSup_proj 𝒜 a).ge (Opens.mem_iSup.2 ⟨m, hy.1.2⟩))
  refine ⟨i + m + l, j + m + l, by push_cast; omega, r * GradedRing.proj 𝒜 m a * p, _,
    SetLike.mul_mem_graded (SetLike.mul_mem_graded hr (SetLike.coe_mem _)) hp, hg,
    homOfLE hgV ≫ iVU, by omega, ?_, ?_⟩
  · simpa [basicOpen_mul] using ⟨⟨hV hxV, hm⟩, hpx⟩
  · rw [op_comp, Functor.map_comp, ConcreteCategory.comp_apply, hs, res_const]
    exact const_ext (by ring)

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
  refine (congr(($(H x)).1 ⟨y.1, hyx⟩) : _).trans ?_
  -- both values are fractions in the localization at `y`, by `const_apply`
  refine Localization.mk_eq_mk_iff.2 (Localization.r_iff_exists.2
    ⟨⟨g x ^ M, fun hgM ↦ hyx (y.1.isPrime.mem_of_pow_mem M hgM)⟩, ?_⟩)
  linear_combination (hgR x).symm

end AlgebraicGeometry.Proj.twistingSheaf

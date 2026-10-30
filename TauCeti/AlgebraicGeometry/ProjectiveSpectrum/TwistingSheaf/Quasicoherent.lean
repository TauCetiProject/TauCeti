/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Away
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.BasicOpen
public import TauCeti.AlgebraicGeometry.Modules.Localization

/-!
# The twisting sheaves are quasi-coherent

Let `A = ⨁ᵢ 𝒜 i` be an `ℕ`-graded commutative ring. This file proves that the twisting sheaves
`𝒪(n)` on `Proj A` are quasi-coherent, for every `n ∈ ℤ` and without assuming that `A` is generated
in degree one (`AlgebraicGeometry.Proj.isQuasicoherent_twistingSheaf`).

The standard opens `D₊(f)`, for `f` homogeneous of positive degree `d`, are affine and cover
`Proj A`. A function on `D₊(f)` is a fraction `a = g / fᵏ` with `g` homogeneous of degree `k d`,
and it is invertible exactly on `D₊(fg)` (`AlgebraicGeometry.Proj.basicOpen_awayToSection_mk`).
Using the description of the sections of `𝒪(n)` over standard opens as fractions
(`AlgebraicGeometry.Proj.twistingSheaf.exists_eq_const_basicOpen` and
`AlgebraicGeometry.Proj.twistingSheaf.const_eq_zero_iff`), we show that the restriction
`Γ(D₊(f), 𝒪(n)) → Γ(D₊(fg), 𝒪(n))` is the localization at `a`. Quasi-coherence then follows from
the affine-local criterion `AlgebraicGeometry.Scheme.Modules.isQuasicoherent_of_isLocalizedModule`.

Since quasi-coherence is local, this is the input needed to show that the twisting sheaves `𝒪(n)`
of a relative `Proj`, which restrict to the twisting sheaves of its charts, are quasi-coherent.

## Main results

* `AlgebraicGeometry.Proj.isQuasicoherent_twistingSheaf`: `𝒪(n)` is quasi-coherent.

## References

* R. Hartshorne, *Algebraic Geometry*, Proposition II.5.11(b).
* [Stacks, Lemma 27.10.3 (01MM)](https://stacks.math.columbia.edu/tag/01MM)
-/

public section

noncomputable section

open CategoryTheory TopologicalSpace HomogeneousLocalization

namespace AlgebraicGeometry.Proj

universe u

variable {A : Type u} {σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable {𝒜 : ℕ → σ} [GradedRing 𝒜] {n : ℤ}

namespace twistingSheaf

/-- A section `c` of the structure sheaf over `U` acts on the sections of `𝒪(n)` over a basic
open `(Proj 𝒜).basicOpen b ≤ U` through its restriction (`Scheme.Modules.moduleBasicOpen`), that
is pointwise through its values in the homogeneous localizations. -/
private theorem smul_basicOpen_apply {U : (Proj 𝒜).Opens} (b c : Γ(Proj 𝒜, U))
    (t : Γ(twistingSheaf 𝒜 n, (Proj 𝒜).basicOpen b)) (x : (Proj 𝒜).basicOpen b) :
    (c • t).1 x = (c.1 ⟨x.1, (Proj 𝒜).basicOpen_le b x.2⟩).val * t.1 x :=
  (rfl)

variable {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) {k : ℕ} {g : A} (hg : g ∈ 𝒜 (k • d))

/-- The powers of the function `g / fᵏ` on `D₊(f)` take the values `(g / fᵏ)ᴺ` in the
localizations. -/
private theorem val_awayToSection_mk_pow_apply (N : ℕ) (y : basicOpen 𝒜 f) :
    (((awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg)) ^ N).1 y).val =
      Localization.mk g ⟨f ^ k, fun h ↦ y.2 (y.1.isPrime.mem_of_pow_mem k h)⟩ ^ N :=
  (congrArg val (Proj.pow_apply _ _ _ N)).trans
    ((val_pow _ _).trans (congrArg (· ^ N) (val_awayToSection_mk_apply ..)))

/-- Every section of `𝒪(n)` over the locus `D₊(fg)` where `a = g / fᵏ` is invertible becomes,
after multiplication by a power of `a`, the restriction of a section over `D₊(f)`. -/
private theorem exists_pow_smul_eq_basicOpenRestrict (hd : 0 < d)
    (t : Γ(twistingSheaf 𝒜 n, (Proj 𝒜).basicOpen (awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg)))) :
    ∃ (m : ℕ) (s : Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 f)),
      awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg) ^ m • t =
        (twistingSheaf 𝒜 n).basicOpenRestrict (awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg)) s := by
  have hV := basicOpen_awayToSection_mk hf k g hg
  -- on `D₊(fg)`, `t` is a fraction `R / (fg)ᵐ`, and `(g / fᵏ)ᵐ • t` is `R / f^(m (k + 1))`
  obtain ⟨m, J, hJ, R, hR, ht⟩ :=
    exists_eq_const_basicOpen (SetLike.mul_mem_graded hf hg) (by omega)
      ((twistingSheaf 𝒜 n).presheaf.map (homOfLE hV.ge).op t)
  refine ⟨m, const (i := (m * (k + 1)) • d) (j := J)
    (by rw [hJ]; simp only [smul_eq_mul]; push_cast; ring) R (f ^ (m * (k + 1))) hR
    (SetLike.pow_mem_graded _ hf) _ (fun x hx h ↦ hx (x.isPrime.mem_of_pow_mem _ h)), ?_⟩
  refine Eq.trans ?_ ((Scheme.Modules.basicOpenRestrict_apply _ _ _).trans (res_const ..)).symm
  refine ext fun x ↦ ?_
  have hx : x.1 ∈ basicOpen 𝒜 (f * g) := hV ▸ x.2
  have e : t.1 x = _ := (res_apply _ t ⟨x.1, hx⟩).symm.trans
    (congr($ht.1 ⟨x.1, hx⟩).trans (const_apply ..))
  refine (smul_basicOpen_apply _ _ t x).trans (Eq.trans ?_ (const_apply ..).symm)
  refine (congrArg₂ (· * ·)
    (val_awayToSection_mk_pow_apply hf hg m ⟨x.1, (Proj 𝒜).basicOpen_le _ x.2⟩) e).trans ?_
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk_iff,
    Localization.r_iff_exists]
  exact ⟨1, by simp; ring⟩

/-- A section of `𝒪(n)` over `D₊(f)` vanishing on the locus `D₊(fg)` where `a = g / fᵏ` is
invertible is killed by a power of `a`. -/
private theorem exists_pow_smul_eq_zero (hd : 0 < d) (s : Γ(twistingSheaf 𝒜 n, basicOpen 𝒜 f))
    (hs : (twistingSheaf 𝒜 n).basicOpenRestrict (awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg)) s = 0) :
    ∃ N : ℕ, awayToSection 𝒜 f (Away.mk 𝒜 hf k g hg) ^ N • s = 0 := by
  have hV := basicOpen_awayToSection_mk hf k g hg
  -- `s` is a fraction `R / fᵐ`; it vanishes on `D₊(fg)`, so `(fg)ᴺ R = 0`, and then
  -- `(g / fᵏ)ᴺ • s = gᴺ R / f^(k N + m)` vanishes on `D₊(f)`
  obtain ⟨m, J, hJ, R, hR, hs'⟩ := exists_eq_const_basicOpen hf hd s
  have hfm : f ^ m ∈ 𝒜 (m * d) := by simpa using SetLike.pow_mem_graded m hf
  have hfgf : basicOpen 𝒜 (f * g) ≤ basicOpen 𝒜 f := hV.ge.trans ((Proj 𝒜).basicOpen_le _)
  have h0 : const hJ R (f ^ m) hR hfm (basicOpen 𝒜 (f * g))
      (fun x hx h ↦ hfgf hx (x.isPrime.mem_of_pow_mem m h)) = 0 := by
    refine (res_const hJ R (f ^ m) hR hfm _ (homOfLE hfgf)).symm.trans
      ((congrArg _ hs'.symm).trans ?_)
    have := congr((twistingSheaf 𝒜 n).presheaf.map (homOfLE hV.ge).op $hs)
    rwa [Scheme.Modules.basicOpenRestrict_apply, map_zero, ← ConcreteCategory.comp_apply,
      ← Functor.map_comp, ← op_comp] at this
  obtain ⟨N, hN⟩ := (const_eq_zero_iff (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜
    (by omega) (SetLike.mul_mem_graded hf hg)) ..).1 h0
  refine ⟨N, ext fun x ↦ ?_⟩
  have e : s.1 x = _ := congr($hs'.1 x).trans (const_apply ..)
  refine (smul_apply _ _ x).trans ((congrArg₂ (· * ·)
    (val_awayToSection_mk_pow_apply hf hg N x) e).trans (Eq.trans ?_ (zero_apply x).symm))
  rw [Localization.mk_pow, Localization.mk_mul, Localization.mk_eq_mk'_apply,
    IsLocalization.mk'_eq_zero_iff]
  exact ⟨⟨f ^ N, fun h ↦ x.2 (x.1.isPrime.mem_of_pow_mem N h)⟩, by linear_combination hN⟩

/-- For `f` homogeneous of positive degree and a function `a` on `D₊(f)`, the restriction of
sections of `𝒪(n)` from `D₊(f)` to the locus `(Proj 𝒜).basicOpen a` where `a` is invertible is
the localization at `a`. Once `isQuasicoherent_twistingSheaf` is available, this is a case of
`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict`. -/
private theorem isLocalizedModule_basicOpenRestrict (hf : f ∈ 𝒜 d) (hd : 0 < d)
    (a : Γ(Proj 𝒜, basicOpen 𝒜 f)) :
    IsLocalizedModule.Away a ((twistingSheaf 𝒜 n).basicOpenRestrict a) := by
  -- `a` is a fraction `g / fᵏ`
  obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (basicOpenIsoAway 𝒜 f hf hd).hom).2 a
  obtain ⟨k, g, hg, rfl⟩ := Away.mk_surjective 𝒜 hf a
  rw [basicOpenIsoAway_hom]
  exact .mk_of_addCommGroup (Scheme.Modules.isUnit_algebraMap_end_basicOpen _ _)
    (exists_pow_smul_eq_basicOpenRestrict hf hg hd) (exists_pow_smul_eq_zero hf hg hd)

end twistingSheaf

variable (𝒜 n) in
/-- **The twisting sheaves `𝒪(n)` are quasi-coherent.** -/
instance isQuasicoherent_twistingSheaf : (twistingSheaf 𝒜 n).IsQuasicoherent :=
  -- the standard opens `D₊(f)`, `f` homogeneous of positive degree, form an affine open cover
  Scheme.Modules.isQuasicoherent_of_isLocalizedModule (ι := {p : A × ℕ // 0 < p.2 ∧ p.1 ∈ 𝒜 p.2})
    _ (fun p ↦ basicOpen 𝒜 p.1.1) (fun p ↦ isAffineOpen_basicOpen 𝒜 p.1.1 p.2.2 p.2.1)
    (eq_top_iff.2 fun x _ ↦ by
      obtain ⟨i, hi, f, hf, hfx⟩ := ProjectiveSpectrum.exists_le_mem_notMem (𝒜 := 𝒜) x 1
      exact Opens.mem_iSup.2 ⟨⟨(f, i), by omega, hf⟩, hfx⟩)
    fun p a ↦ twistingSheaf.isLocalizedModule_basicOpenRestrict p.2.2 p.2.1 a

end AlgebraicGeometry.Proj

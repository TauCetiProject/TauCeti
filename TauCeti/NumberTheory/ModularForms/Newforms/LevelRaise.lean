/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.RingEigenvalue
import TauCeti.NumberTheory.ModularForms.Newforms.EigenFromPrimes

/-!
# Level-raising bundled good Hecke eigenforms

For a good Hecke eigenform `f : EigenformAwayFromLevel M k` and a multiple `N` of `M`, every
level-raise `V_d f` with `d * M ∣ N` lies in the character space of `f.χ.comp (unitsMap hMN)` and
is an eigenvector of `T_p` with eigenvalue `f.eigenvalue p` at every prime `p ∤ N`. By linearity,
any nonzero cusp form `F` in the span of `{V_d f | d * M ∣ N}` shares that nebentypus and those
good-prime eigenvalues, so `EigenformAwayFromLevel.ofForallPrime` bundles `F` into a good Hecke
eigenform at level `N` whose eigenvalues at all indices coprime to `N` agree with those of `f`.

Specialising to a single generator `V_d f` (nonzero by injectivity of `CuspForm.levelRaiseₗ`) gives
the bundled level-raising operator `EigenformAwayFromLevel.levelRaise`, together with its identity
(`V₁ f = f`) and composition (`V_d (V_e f) = V_{e * d} f`) laws.

## Main definitions (in `HeckeRing.GL2.EigenformAwayFromLevel`)

* `ofMemSpanLevelRaise`: bundle any nonzero cusp form in `span {V_d f | d * M ∣ N}` as a good Hecke
  eigenform at level `N`.
* `levelRaise`: raise a bundled good Hecke eigenform along `d * M ∣ N`.

## Main results (in `HeckeRing.GL2.EigenformAwayFromLevel`)

* `ofMemSpanLevelRaise_toCuspForm`, `ofMemSpanLevelRaise_χ`, `ofMemSpanLevelRaise_eigenvalue`:
  underlying cusp form, induced nebentypus, and eigenvalues of `ofMemSpanLevelRaise`.
* `levelRaise_toCuspForm`, `levelRaise_χ`, `levelRaise_eigenvalue`, `levelRaise_one_self`,
  `levelRaise_levelRaise`: characteristic API and functoriality of `levelRaise`.

## References

* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005], §5.8.
* [T. Miyake, *Modular forms*][miyake1989], §4.6.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup ZMod TauCeti

open scoped MatrixGroups ModularForm

namespace HeckeRing.GL2.EigenformAwayFromLevel

variable {M N L : ℕ} {k : ℤ}

/-- Every cusp form in the level-raise span of `f` has nebentypus induced by `f.χ` and is an
eigenvector of `T_p` for every prime `p ∤ N` with eigenvalue `f.eigenvalue p`. -/
private theorem mem_charSpace_and_heckeTCuspNat_of_mem_span_levelRaise [NeZero M] [NeZero N]
    (f : EigenformAwayFromLevel M k) (hMN : M ∣ N)
    {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ Submodule.span ℂ {G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∃ (d : ℕ) (_ : NeZero d) (h : d * M ∣ N),
        CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f.toCuspForm = G}) :
    F ∈ cuspFormCharSpace k (f.χ.comp (unitsMap hMN)) ∧
      ∀ (p : ℕ) (hp : p.Prime) (hpN : Nat.Coprime p N),
        heckeTCuspNat k p (_hn := ⟨hp.ne_zero⟩) F =
          f.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hMN) • F := by
  refine ⟨Submodule.span_le.mpr ?_ hF, fun p hp hpN ↦ ?_⟩
  · rintro _ ⟨d, _, hd, rfl⟩
    exact CuspForm.levelRaise_mem_cuspFormCharSpace_of_dvd hd f.χ f.mem_charSpace
  · have : NeZero p := ⟨hp.ne_zero⟩
    refine Module.End.mem_eigenspace_iff.mp (Submodule.span_le.mpr ?_ hF)
    rintro _ ⟨d, _, hd, rfl⟩
    exact Module.End.mem_eigenspace_iff.mpr
      (f.heckeTCuspNat_levelRaise_eq_eigenvalue_smul hd hp hpN)

/-- **Bundle any nonzero cusp form in the level-raise span of `f` as a good Hecke eigenform.**
For `M ∣ N` and any nonzero `F` in `span {V_d f | d * M ∣ N}`, `F` inherits the induced nebentypus
and the good eigenvalues of `f`. -/
noncomputable def ofMemSpanLevelRaise [NeZero M] [NeZero N] (f : EigenformAwayFromLevel M k)
    (hMN : M ∣ N) {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ Submodule.span ℂ {G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∃ (d : ℕ) (_ : NeZero d) (h : d * M ∣ N),
        CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f.toCuspForm = G})
    (hF0 : F ≠ 0) : EigenformAwayFromLevel N k :=
  let hprop := mem_charSpace_and_heckeTCuspNat_of_mem_span_levelRaise f hMN hF
  ofForallPrime hprop.1 hF0 fun p hp hpN ↦
    have : NeZero p := ⟨hp.ne_zero⟩
    ⟨f.eigenvalue ⟨p, hp.pos⟩ (hpN.coprime_dvd_right hMN), by
      rw [← heckeTCompositeGamma0_prime N hp]
      exact heckeRingHomCuspCharSpace_heckeTCompositeGamma0_eq_smul_of_heckeTCuspNat_eq_smul hp
        (hprop.2 p hp hpN)⟩

/-- The underlying cusp form of `f.ofMemSpanLevelRaise` is `F`. -/
@[simp]
theorem ofMemSpanLevelRaise_toCuspForm [NeZero M] [NeZero N] (f : EigenformAwayFromLevel M k)
    (hMN : M ∣ N) {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ Submodule.span ℂ {G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∃ (d : ℕ) (_ : NeZero d) (h : d * M ∣ N),
        CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f.toCuspForm = G})
    (hF0 : F ≠ 0) :
    (f.ofMemSpanLevelRaise hMN hF hF0).toCuspForm = F := by
  rw [ofMemSpanLevelRaise, ofForallPrime_toCuspForm]

/-- The nebentypus of `f.ofMemSpanLevelRaise` is `f.χ` pulled back to `(ZMod N)ˣ`. -/
@[simp]
theorem ofMemSpanLevelRaise_χ [NeZero M] [NeZero N] (f : EigenformAwayFromLevel M k)
    (hMN : M ∣ N) {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ Submodule.span ℂ {G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∃ (d : ℕ) (_ : NeZero d) (h : d * M ∣ N),
        CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f.toCuspForm = G})
    (hF0 : F ≠ 0) :
    (f.ofMemSpanLevelRaise hMN hF hF0).χ = f.χ.comp (unitsMap hMN) := by
  rw [ofMemSpanLevelRaise, ofForallPrime_χ]

-- Not `@[simp]`: the proof `hm` appears only on the right-hand side.
/-- The eigenvalues of `ofMemSpanLevelRaise` at all good indices agree with those of `f`. -/
theorem ofMemSpanLevelRaise_eigenvalue [NeZero M] [NeZero N] (f : EigenformAwayFromLevel M k)
    (hMN : M ∣ N) {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hF : F ∈ Submodule.span ℂ {G : CuspForm ((Gamma1 N).map (mapGL ℝ)) k |
      ∃ (d : ℕ) (_ : NeZero d) (h : d * M ∣ N),
        CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f.toCuspForm = G})
    (hF0 : F ≠ 0) (n : ℕ+) (hn : Nat.Coprime (n : ℕ) N) (hm : Nat.Coprime (n : ℕ) M) :
    (f.ofMemSpanLevelRaise hMN hF hF0).eigenvalue n hn = f.eigenvalue n hm := by
  symm
  refine eigenvalue_eq_of_comp_unitsMap_eq_of_forall_prime f (f.ofMemSpanLevelRaise hMN hF hF0)
    hMN (f.ofMemSpanLevelRaise_χ hMN hF hF0).symm (fun p hp hpN ↦ ?_) n hm hn
  have : NeZero p := ⟨hp.ne_zero⟩
  have h1 := (f.ofMemSpanLevelRaise hMN hF hF0).heckeTCuspNat_eq_eigenvalue_smul hp hpN
  have h2 := (mem_charSpace_and_heckeTCuspNat_of_mem_span_levelRaise f hMN hF).2 p hp hpN
  rw [f.ofMemSpanLevelRaise_toCuspForm] at h1
  exact smul_left_injective ℂ hF0 (h2.symm.trans h1)

/-- **Raise the level of a bundled good Hecke eigenform** along `d * M ∣ N`: the degeneracy image
`V_d f` as an `EigenformAwayFromLevel N k`. -/
noncomputable def levelRaise [NeZero M] [NeZero N] (d : ℕ) [NeZero d] (h : d * M ∣ N)
    (f : EigenformAwayFromLevel M k) : EigenformAwayFromLevel N k :=
  f.ofMemSpanLevelRaise (dvd_of_mul_left_dvd h)
    (Submodule.subset_span ⟨d, inferInstance, h, rfl⟩)
    (by
      rw [← CuspForm.levelRaiseₗ_apply]
      exact (map_ne_zero_iff _ (CuspForm.levelRaiseₗ_injective _)).mpr f.ne_zero)

/-- The underlying cusp form of `f.levelRaise d h` is `CuspForm.levelRaise d _ f.toCuspForm`. -/
@[simp]
theorem levelRaise_toCuspForm [NeZero M] [NeZero N] (d : ℕ) [NeZero d] (h : d * M ∣ N)
    (f : EigenformAwayFromLevel M k) :
    (f.levelRaise d h).toCuspForm =
      CuspForm.levelRaise d (Gamma1_map_le_conjAct_scaleGL_of_dvd h) f.toCuspForm := by
  rw [levelRaise, ofMemSpanLevelRaise_toCuspForm]

/-- The nebentypus of `f.levelRaise d h` is `f.χ` pulled back to `(ZMod N)ˣ`. -/
@[simp]
theorem levelRaise_χ [NeZero M] [NeZero N] (d : ℕ) [NeZero d] (h : d * M ∣ N)
    (f : EigenformAwayFromLevel M k) :
    (f.levelRaise d h).χ = f.χ.comp (unitsMap (dvd_of_mul_left_dvd h)) := by
  rw [levelRaise, ofMemSpanLevelRaise_χ]

-- Not `@[simp]`: the proof `hm` appears only on the right-hand side.
/-- Raising the level preserves the eigenvalue at every index coprime to the raised level. -/
theorem levelRaise_eigenvalue [NeZero M] [NeZero N] (d : ℕ) [NeZero d] (h : d * M ∣ N)
    (f : EigenformAwayFromLevel M k) (n : ℕ+)
    (hn : Nat.Coprime (n : ℕ) N) (hm : Nat.Coprime (n : ℕ) M) :
    (f.levelRaise d h).eigenvalue n hn = f.eigenvalue n hm :=
  f.ofMemSpanLevelRaise_eigenvalue _ _ _ n hn hm

/-- Raising a good Hecke eigenform by `V₁` to its own level returns the eigenform unchanged. -/
@[simp]
theorem levelRaise_one_self [NeZero N] (h : 1 * N ∣ N) (f : EigenformAwayFromLevel N k) :
    f.levelRaise 1 h = f := by
  ext1
  rw [levelRaise_toCuspForm]
  exact _root_.CuspForm.levelRaise_one_self _ f.toCuspForm

/-- Iterated level-raising of bundled good Hecke eigenforms composes by multiplying the dilation
factors. -/
@[simp]
theorem levelRaise_levelRaise [NeZero M] [NeZero N] [NeZero L] {d e : ℕ} [NeZero d] [NeZero e]
    (he : e * M ∣ N) (hd : d * N ∣ L) (f : EigenformAwayFromLevel M k) :
    (f.levelRaise e he).levelRaise d hd =
      f.levelRaise (e * d)
        (by rw [mul_comm e d, mul_assoc]; exact (mul_dvd_mul_left d he).trans hd) := by
  ext1
  rw [levelRaise_toCuspForm, levelRaise_toCuspForm, levelRaise_toCuspForm,
    CuspForm.levelRaise_levelRaise]

end HeckeRing.GL2.EigenformAwayFromLevel

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.Descent.CuspForm
public import TauCeti.NumberTheory.ModularForms.Newforms.FullEigenform
public import TauCeti.NumberTheory.ModularForms.Newforms.OrthogonalBasis

/-!
# Vanishing of the bad-prime eigenvalue when `p² ∣ N` and `χ` is defined modulo `N / p`

For a prime `p` with `p² ∣ N` and a nebentypus `χ` defined modulo `N / p`, the operator `U_p` on
`S_k(N, χ)` lowers the level: `U_p f` is a cusp form of level `Γ₁(N / p)`. Since `p ∣ N / p`, the
`p` upper-triangular matrices `[1, b; 0, p]` defining `U_p` are exactly Miyake's descent family at
`p² ∣ N`, whose slash sum is `Γ₀(N / p)`-equivariant with the lowered nebentypus
(`TauCeti.descendCuspForm`). So `U_p f` is old.

For a newform `f` this forces `a_p(f) = 0`: `U_p f = a_p(f) • f` is both old and new, hence zero,
while `f ≠ 0`. This is the vanishing case of the classification of the bad-prime eigenvalues of a
newform (Atkin–Lehner for trivial nebentypus, Li in general; Miyake, Theorem 4.6.17): in terms of
`c = v_p(cond χ)`, the hypotheses say `v_p(N) ≥ 2` and `c < v_p(N)`. In the remaining cases the
classification gives `a_p ≠ 0`; those cases are not treated here. Since the newforms of
nebentypus `χ` span the new part of `S_k(N, χ)`, `U_p` is zero on that whole new part.

## Main results

* `HeckeRing.GL2.heckeUCuspNat_eq_ofLe_descendCuspForm`: for `p² ∣ N` and `χ` pulled back from
  `χ₀` modulo `N / p`, `U_p f` is the descent of `f`, a cusp form in `S_k(Γ₁(N / p), χ₀)`, read
  at level `N`.
* `HeckeRing.GL2.heckeUCuspNat_mem_cuspFormsOld_of_sq_dvd`: in that situation `U_p f` is old.
* `HeckeRing.GL2.Newform.qExpansion_coeff_prime_eq_zero_of_sq_dvd`: a newform whose nebentypus
  factors through `N / p`, with `p² ∣ N`, has `a_p = 0`.
* `HeckeRing.GL2.heckeUCuspNat_eq_zero_of_mem_cuspFormsNew_of_sq_dvd`: `U_p` vanishes on the new
  part of `S_k(N, χ)` when `p² ∣ N` and `χ` factors through `N / p`.

## References

* [T. Miyake, *Modular forms*][miyake1989], Lemma 4.6.14 and Theorem 4.6.17.
* A. O. L. Atkin and J. Lehner, *Hecke operators on `Γ₀(m)`*, Math. Ann. **185** (1970),
  134–160.
* W.-C. W. Li, *Newforms and functional equations*, Math. Ann. **212** (1975), 285–315.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N p : ℕ} [NeZero N] {k : ℤ}

/-! ### `U_p` lowers the level -/

variable (k) in
/-- **`U_p` lowers the level when `p² ∣ N` and the nebentypus is defined modulo `N / p`.** For
`f ∈ S_k(Γ₁(N), χ)` with `χ` the pull-back of `χ₀` modulo `N / p`, the form `U_p f` is the descent
`descendCuspForm` of `f`, a cusp form in `S_k(Γ₁(N / p), χ₀)`
(`descendCuspForm_mem_cuspFormCharSpace`), read at level `N`. -/
theorem heckeUCuspNat_eq_ofLe_descendCuspForm (hp : p.Prime) (hpsq : p ^ 2 ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp
      (ZMod.unitsMap (Nat.div_dvd_of_dvd ((dvd_pow_self p two_ne_zero).trans hpsq))))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    heckeUCuspNat k p hp ((dvd_pow_self p two_ne_zero).trans hpsq) f =
      _root_.CuspForm.ofLe
        (Gamma1_map_le_Gamma1_map_of_dvd
          (Nat.div_dvd_of_dvd ((dvd_pow_self p two_ne_zero).trans hpsq)))
        (descendCuspForm k hp ((dvd_pow_self p two_ne_zero).trans hpsq) hcomp hf) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  ext τ
  rw [_root_.CuspForm.coe_ofLe, coe_descendCuspForm, descendSlash_eq_heckeSlashUpperTri k hpsq,
    heckeUCuspNat_eq_heckeTCuspNat,
    heckeTCuspNat_eq_upperTri k ((dvd_pow_self p two_ne_zero).trans hpsq),
    coe_heckeSlashUpperTriCuspFormEnd]

variable (k) in
/-- **`U_p` maps into the old subspace when `p² ∣ N` and the nebentypus is defined modulo
`N / p`**: `U_p f` comes from the proper divisor level `N / p`
(`heckeUCuspNat_eq_ofLe_descendCuspForm`). -/
theorem heckeUCuspNat_mem_cuspFormsOld_of_sq_dvd (hp : p.Prime) (hpsq : p ^ 2 ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} {χ₀ : (ZMod (N / p))ˣ →* ℂˣ}
    (hcomp : χ = χ₀.comp
      (ZMod.unitsMap (Nat.div_dvd_of_dvd ((dvd_pow_self p two_ne_zero).trans hpsq))))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k} (hf : f ∈ cuspFormCharSpace k χ) :
    heckeUCuspNat k p hp ((dvd_pow_self p two_ne_zero).trans hpsq) f ∈ cuspFormsOld N k := by
  rw [heckeUCuspNat_eq_ofLe_descendCuspForm k hp hpsq hcomp hf]
  exact ofLe_mem_cuspFormsOld (Nat.div_dvd_of_dvd ((dvd_pow_self p two_ne_zero).trans hpsq))
    (Nat.div_lt_self (NeZero.pos N) hp.one_lt).ne k _

/-! ### The vanishing of `a_p` -/

/-- **A newform has `a_p = 0` when `p² ∣ N` and its nebentypus is defined modulo `N / p`**
(Atkin–Lehner for trivial nebentypus; Li; Miyake, Theorem 4.6.17). With
`Newform.heckeUCuspNat_eq_qExpansion_coeff_smul` this says `U_p f = 0`. -/
theorem Newform.qExpansion_coeff_prime_eq_zero_of_sq_dvd (f : Newform N k) (hp : p.Prime)
    (hpsq : p ^ 2 ∣ N) (hχ : f.dirichletLift.FactorsThrough (N / p)) :
    (qExpansion 1 f.toCuspForm).coeff p = 0 := by
  have hpN : p ∣ N := (dvd_pow_self p two_ne_zero).trans hpsq
  -- the nebentypus is the pull-back of the lowered character `hχ.χ₀`
  have hcomp : f.χ = hχ.χ₀.toUnitHom.comp (ZMod.unitsMap (Nat.div_dvd_of_dvd hpN)) := by
    rw [← f.dirichletLift_equivToUnitHom, ← MulChar.toUnitHom_eq]
    conv_lhs => rw [hχ.eq_changeLevel]
    rw [DirichletCharacter.changeLevel_toUnitHom]
  -- the eigenvector `U_p f = a_p(f) • f` is old, and it is new, so it vanishes
  have hold := heckeUCuspNat_mem_cuspFormsOld_of_sq_dvd k hp hpsq hcomp f.mem_charSpace
  rw [f.heckeUCuspNat_eq_qExpansion_coeff_smul hp hpN] at hold
  have h0 := Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew N k) _ hold
    (Submodule.smul_mem _ _ f.isNew)
  exact (smul_eq_zero.mp h0).resolve_right f.ne_zero

variable (k) in
/-- **`U_p` vanishes on the new part of `S_k(N, χ)` when `p² ∣ N` and `χ` is defined modulo
`N / p`.** In particular the new part of `S_k(N, χ)` is `U_p`-stable in this case. -/
theorem heckeUCuspNat_eq_zero_of_mem_cuspFormsNew_of_sq_dvd (hp : p.Prime) (hpsq : p ^ 2 ∣ N)
    {χ : (ZMod N)ˣ →* ℂˣ} (hχ : DirichletCharacter.FactorsThrough (MulChar.ofUnitHom χ) (N / p))
    {f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hf : f ∈ cuspFormsNew N k ⊓ cuspFormCharSpace k χ) :
    heckeUCuspNat k p hp ((dvd_pow_self p two_ne_zero).trans hpsq) f = 0 := by
  have hpN : p ∣ N := (dvd_pow_self p two_ne_zero).trans hpsq
  -- the newforms of nebentypus `χ` span the new part, and `U_p` kills each of them
  rw [← Newform.span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace] at hf
  refine (Submodule.span_le (p := LinearMap.ker (heckeUCuspNat k p hp hpN))).mpr ?_ hf
  rintro _ ⟨g, rfl, rfl⟩
  rw [← g.dirichletLift_def] at hχ
  rw [SetLike.mem_coe, LinearMap.mem_ker, g.heckeUCuspNat_eq_qExpansion_coeff_smul hp hpN,
    g.qExpansion_coeff_prime_eq_zero_of_sq_dvd hp hpsq hχ, zero_smul]

end HeckeRing.GL2

end

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ModularForms.Newforms.HeckeStability
public import TauCeti.NumberTheory.ModularForms.Newforms.Nebentypus
public import TauCeti.NumberTheory.ModularForms.Newforms.StrongMultiplicityOne
public import TauCeti.NumberTheory.ModularForms.Petersson.Eigenbasis
import TauCeti.NumberTheory.ModularForms.SturmBound

/-!
# The newforms are an orthogonal basis of the new subspace

The newforms of level `N` and weight `k` form a Petersson-orthogonal basis of the new subspace
`S_k(Γ₁(N))ⁿᵉʷ`, and those of nebentypus `χ` span its `χ`-part `S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)`.

*Orthogonality.* Good Hecke eigenforms whose eigenvalues differ at a prime `p ∤ N` are
orthogonal: for a common nebentypus `χ` because the Petersson adjoint of `Tₚ` on `S_k(N, χ)` is
`χ(p)⁻¹ Tₚ`, and otherwise because the nebentypus decomposition is orthogonal. Two distinct
newforms differ in nebentypus or at some good prime, since a newform is determined by its
nebentypus and its eigenvalues at the good primes.

*Spanning.* `S_k(N, χ)` has a basis of good Hecke eigenforms, and its old and new parts are
stable under the good `Tₚ` and complementary. So the new part of each basis vector is again a
good Hecke eigenvector, and these new parts span `S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)`. A nonzero good
Hecke eigenvector in the new subspace has `a₁ ≠ 0`, so dividing by `a₁` makes it a newform.

## Main definitions

* `HeckeRing.GL2.Newform.ofForallPrime`: a nonzero cusp form of nebentypus `χ` in the new
  subspace that is an eigenvector of every good `Tₚ`, divided by its first coefficient, as a
  newform.
* `HeckeRing.GL2.Newform.basis`: the newforms, as a basis of `S_k(Γ₁(N))ⁿᵉʷ`.

## Main results

* `HeckeRing.GL2.EigenformAwayFromLevel.peterssonInnerCosets_eq_zero_of_eigenvalue_ne`: good
  Hecke eigenforms with distinct eigenvalues at a good prime are orthogonal.
* `HeckeRing.GL2.Newform.peterssonInnerCosets_eq_zero_of_ne`: distinct newforms are orthogonal.
* `HeckeRing.GL2.Newform.span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace`: the
  newforms of nebentypus `χ` span `S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)`.
* `HeckeRing.GL2.Newform.span_range_toCuspForm_eq_cuspFormsNew`: the newforms span `S_k(Γ₁(N))ⁿᵉʷ`.
* `HeckeRing.GL2.Newform.linearIndependent_toCuspForm`: the newforms are linearly independent.

## References

* [T. Miyake, *Modular forms*][miyake1989], Theorem 4.6.13(2).
* [F. Diamond and J. Shurman, *A first course in modular forms*][diamondshurman2005],
  Theorem 5.8.2.
-/

public section

open Matrix.SpecialLinearGroup UpperHalfPlane CongruenceSubgroup TauCeti ComplexConjugate

open scoped MatrixGroups

namespace HeckeRing.GL2

variable {N : ℕ} [NeZero N] {k : ℤ} {χ : (ZMod N)ˣ →* ℂˣ}

/-! ### Orthogonality -/

namespace EigenformAwayFromLevel

/-- A good Hecke eigenform of nebentypus `χ`, seen in `S_k(N, χ)`, is an eigenvector of the Hecke
ring generator `Tₚ` at every prime `p` not dividing `N`, with its eigenvalue at `p`. -/
private theorem heckeRingHomCuspCharSpace_heckeTGeneratorGamma0_eq_smul
    {f : EigenformAwayFromLevel N k} {x : cuspFormCharSpace k χ} (hχ : f.χ = χ)
    (hx : f.toCuspForm = (x : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)) {p : ℕ} (hp : p.Prime)
    (hpN : Nat.Coprime p N) :
    heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) x =
      f.eigenvalue ⟨p, hp.pos⟩ hpN • x := by
  obtain ⟨F, χ', hF, a, haF, _⟩ := f
  obtain rfl : χ' = χ := hχ
  obtain rfl : ⟨F, hF⟩ = x := Subtype.ext hx
  simpa only [PNat.mk_coe, heckeTCompositeGamma0_prime N hp] using haF ⟨p, hp.pos⟩ hpN

/-- **Good Hecke eigenforms with distinct eigenvalues are orthogonal.** Two good Hecke
eigenforms whose eigenvalues differ at a prime `p` not dividing `N` are Petersson-orthogonal. -/
theorem peterssonInnerCosets_eq_zero_of_eigenvalue_ne {f g : EigenformAwayFromLevel N k}
    {p : ℕ} (hp : p.Prime) (hpN : Nat.Coprime p N)
    (hne : f.eigenvalue ⟨p, hp.pos⟩ hpN ≠ g.eigenvalue ⟨p, hp.pos⟩ hpN) :
    CuspForm.peterssonInnerCosets f.toCuspForm g.toCuspForm = 0 := by
  -- forms of distinct nebentypus are orthogonal
  obtain hχ | hχ := ne_or_eq f.χ g.χ
  · exact CuspForm.peterssonInnerCosets_eq_zero_of_mem_cuspFormCharSpace_of_ne hχ
      f.mem_charSpace g.mem_charSpace
  -- the adjoint `χ(p)⁻¹ Tₚ` of `Tₚ`, evaluated on two eigenvectors
  have key (x y : cuspFormCharSpace k g.χ) (α β : ℂ)
      (hx : heckeRingHomCuspCharSpace k g.χ (heckeTGeneratorGamma0 N p) x = α • x)
      (hy : heckeRingHomCuspCharSpace k g.χ (heckeTGeneratorGamma0 N p) y = β • y) :
      (α - conj ((g.χ (ZMod.unitOfCoprime p hpN) : ℂ)⁻¹ * β)) *
        CuspForm.peterssonInnerCosets (y : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) x = 0 := by
    have hadj := isAdjointPair_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0 (χ := g.χ) k hp
      hpN x y
    simp only [LinearMap.flip_apply,
      TauCeti.CuspForm.peterssonInnerCosetsCharSpaceₛₗ_apply_apply, Pi.smul_apply, hx, hy,
      Submodule.coe_smul, CuspForm.peterssonInnerCosets_smul_left,
      CuspForm.peterssonInnerCosets_smul_right] at hadj
    rw [map_mul]
    linear_combination hadj
  let x : cuspFormCharSpace k g.χ := ⟨f.toCuspForm, hχ ▸ f.mem_charSpace⟩
  let y : cuspFormCharSpace k g.χ := ⟨g.toCuspForm, g.mem_charSpace⟩
  have hx := heckeRingHomCuspCharSpace_heckeTGeneratorGamma0_eq_smul (x := x) hχ rfl hp hpN
  have hy := heckeRingHomCuspCharSpace_heckeTGeneratorGamma0_eq_smul (x := y) rfl rfl hp hpN
  -- `g` pairs nontrivially with itself, so its eigenvalue is fixed by `c ↦ conj (χ(p)⁻¹ * c)`
  have hfix : conj ((g.χ (ZMod.unitOfCoprime p hpN) : ℂ)⁻¹ * g.eigenvalue ⟨p, hp.pos⟩ hpN) =
      g.eigenvalue ⟨p, hp.pos⟩ hpN :=
    (sub_eq_zero.mp ((mul_eq_zero.mp (key y y _ _ hy hy)).resolve_right
      (mt (CuspForm.peterssonInnerCosets_self_eq_zero _).mp g.ne_zero))).symm
  have hyx := key x y _ _ hx hy
  rw [hfix] at hyx
  rw [← CuspForm.peterssonInnerCosets_conj_symm, (mul_eq_zero.mp hyx).resolve_left
    (sub_ne_zero.mpr hne), map_zero]

end EigenformAwayFromLevel

namespace Newform

/-- **Distinct newforms are orthogonal**: the Petersson product of two distinct newforms of level
`N` and weight `k`, of the same or of different nebentypus, vanishes. -/
theorem peterssonInnerCosets_eq_zero_of_ne {f g : Newform N k} (h : f ≠ g) :
    CuspForm.peterssonInnerCosets f.toCuspForm g.toCuspForm = 0 := by
  by_contra h0
  have hχ : f.χ = g.χ := by_contra fun hχ ↦ h0
    (CuspForm.peterssonInnerCosets_eq_zero_of_mem_cuspFormCharSpace_of_ne hχ f.mem_charSpace
      g.mem_charSpace)
  exact h (eq_of_forall_prime_eigenvalue_eq hχ fun p hp hpN ↦ by_contra fun hne ↦
    h0 (EigenformAwayFromLevel.peterssonInnerCosets_eq_zero_of_eigenvalue_ne hp hpN hne))

/-- **The newforms are linearly independent**: the underlying cusp forms of the newforms of level
`N` and weight `k` are linearly independent. -/
theorem linearIndependent_toCuspForm :
    LinearIndependent ℂ (fun f : Newform N k ↦ f.toCuspForm) :=
  LinearMap.linearIndependent_of_isOrthoᵢ (B := TauCeti.CuspForm.peterssonInnerCosetsₛₗ)
    (LinearMap.isOrthoᵢ_def.mpr fun _ _ h ↦ by
      simpa using peterssonInnerCosets_eq_zero_of_ne h)
    fun f ↦ by simpa [CuspForm.peterssonInnerCosets_self_eq_zero] using f.ne_zero

/-! ### Normalising a new eigenvector -/

/-- A nonzero good Hecke eigenvector in the new subspace has nonzero first coefficient. -/
private theorem qExpansion_coeff_one_ne_zero {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hχ : F ∈ cuspFormCharSpace k χ) (hnew : F ∈ cuspFormsNew N k) (hF : F ≠ 0)
    (h : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨F, hχ⟩ = c • ⟨F, hχ⟩) :
    (qExpansion 1 F).coeff 1 ≠ 0 := fun h1 ↦
  hF (eq_zero_of_forall_prime_heckeRingHomCusp_of_one_eq_zero_of_mem_cuspFormsNew (F := ⟨F, hχ⟩)
    (fun p hp hpN ↦ by rw [heckeTCompositeGamma0_prime N hp]; exact h p hp hpN) h1 hnew)

/-- **A new eigenvector, normalised, is a newform.** A nonzero cusp form of nebentypus `χ` in the
new subspace that is an eigenvector of the Hecke ring at every prime not dividing `N`, divided
by its first coefficient (which is nonzero). -/
noncomputable def ofForallPrime {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hχ : F ∈ cuspFormCharSpace k χ) (hnew : F ∈ cuspFormsNew N k) (hF : F ≠ 0)
    (h : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨F, hχ⟩ = c • ⟨F, hχ⟩) :
    Newform N k where
  toEigenformAwayFromLevel :=
    EigenformAwayFromLevel.ofForallPrime (f := ((qExpansion 1 F).coeff 1)⁻¹ • F)
      (Submodule.smul_mem _ _ hχ)
      (smul_ne_zero (inv_ne_zero (qExpansion_coeff_one_ne_zero hχ hnew hF h)) hF)
      fun p hp hpN ↦ by
        obtain ⟨c, hc⟩ := h p hp hpN
        -- the rescaled form, as an element of `S_k(N, χ)`, is the rescaled element
        have hmk : (⟨((qExpansion 1 F).coeff 1)⁻¹ • F, Submodule.smul_mem _ _ hχ⟩ :
            cuspFormCharSpace k χ) = ((qExpansion 1 F).coeff 1)⁻¹ • ⟨F, hχ⟩ :=
          Subtype.ext (Submodule.coe_smul _ (⟨F, hχ⟩ : cuspFormCharSpace k χ)).symm
        exact ⟨c, by rw [hmk, map_smul, hc, smul_comm]⟩
  isNew := by
    rw [EigenformAwayFromLevel.ofForallPrime_toCuspForm]
    exact Submodule.smul_mem _ _ hnew
  isNorm := by
    rw [EigenformAwayFromLevel.ofForallPrime_toCuspForm,
      ← CuspForm.qExpansionCoeffₗ_apply one_pos (one_mem_strictPeriods_Gamma1_map N), map_smul,
      CuspForm.qExpansionCoeffₗ_apply, smul_eq_mul,
      inv_mul_cancel₀ (qExpansion_coeff_one_ne_zero hχ hnew hF h)]

/-- The underlying cusp form of `ofForallPrime` is the supplied form divided by its first
coefficient. -/
@[simp]
theorem ofForallPrime_toCuspForm {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hχ : F ∈ cuspFormCharSpace k χ) (hnew : F ∈ cuspFormsNew N k) (hF : F ≠ 0)
    (h : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨F, hχ⟩ = c • ⟨F, hχ⟩) :
    (ofForallPrime hχ hnew hF h).toCuspForm = ((qExpansion 1 F).coeff 1)⁻¹ • F :=
  EigenformAwayFromLevel.ofForallPrime_toCuspForm _ _ _

/-- The nebentypus of `ofForallPrime` is the character supplied to the constructor. -/
@[simp]
theorem ofForallPrime_χ {F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k}
    (hχ : F ∈ cuspFormCharSpace k χ) (hnew : F ∈ cuspFormsNew N k) (hF : F ≠ 0)
    (h : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) ⟨F, hχ⟩ = c • ⟨F, hχ⟩) :
    (ofForallPrime hχ hnew hF h).χ = χ :=
  EigenformAwayFromLevel.ofForallPrime_χ _ _ _

/-! ### Spanning -/

/-- A good Hecke eigenvector in the new part of `S_k(N, χ)` lies in the span of the newforms of
nebentypus `χ`: it is zero or a multiple of the newform `ofForallPrime`. -/
private theorem mem_span_of_forall_prime {F : cuspFormCharSpace k χ}
    (hnew : (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k)
    (h : ∀ p : ℕ, p.Prime → Nat.Coprime p N → ∃ c : ℂ,
      heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) F = c • F) :
    (F : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      Submodule.span ℂ ((fun f : Newform N k ↦ f.toCuspForm) '' {f | f.χ = χ}) := by
  obtain ⟨F, hχ⟩ := F
  rcases eq_or_ne F 0 with rfl | hF
  · exact Submodule.zero_mem _
  have hmem : (ofForallPrime hχ hnew hF h).toCuspForm ∈
      Submodule.span ℂ ((fun f : Newform N k ↦ f.toCuspForm) '' {f | f.χ = χ}) :=
    Submodule.subset_span ⟨_, ofForallPrime_χ hχ hnew hF h, rfl⟩
  rw [ofForallPrime_toCuspForm] at hmem
  simpa [smul_inv_smul₀ (qExpansion_coeff_one_ne_zero hχ hnew hF h)] using
    Submodule.smul_mem _ ((qExpansion 1 F).coeff 1) hmem

/-- The new part of a good Hecke eigenvector is a good Hecke eigenvector, with the same
eigenvalue: the old and new parts of `S_k(N, χ)` are both stable under the good `Tₚ`, and they
meet only in `0`. -/
private theorem heckeRingHomCuspCharSpace_eq_smul_of_add_eq {p : ℕ} (hp : p.Prime)
    (hpN : Nat.Coprime p N) {x o n : cuspFormCharSpace k χ}
    (ho : (o : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsOld N k)
    (hn : (n : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k) (hx : o + n = x)
    {c : ℂ} (hc : heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) x = c • x) :
    heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p) n = c • n := by
  set T := heckeRingHomCuspCharSpace k χ (heckeTGeneratorGamma0 N p)
  have hd : T n - c • n = c • o - T o := by
    rw [sub_eq_sub_iff_add_eq_add, add_comm, ← map_add, hx, hc, ← hx, smul_add, add_comm]
  have hzero := (Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew N k))
    ((T n - c • n : cuspFormCharSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (by
      rw [hd, Submodule.coe_sub, Submodule.coe_smul]
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ho)
        (coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0_mem_cuspFormsOld hp hpN ho))
    (by
      rw [Submodule.coe_sub, Submodule.coe_smul]
      exact Submodule.sub_mem _
        (coe_heckeRingHomCuspCharSpace_heckeTGeneratorGamma0_mem_cuspFormsNew hp hpN hn)
        (Submodule.smul_mem _ _ hn))
  exact sub_eq_zero.mp (Submodule.coe_eq_zero.mp hzero)

/-- **The newforms of nebentypus `χ` span the new part of `S_k(N, χ)`** (Miyake,
Theorem 4.6.13(2)): the span of their underlying cusp forms is `S_k(Γ₁(N))ⁿᵉʷ ⊓ S_k(N, χ)`. -/
theorem span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace (χ : (ZMod N)ˣ →* ℂˣ) :
    Submodule.span ℂ ((fun f : Newform N k ↦ f.toCuspForm) '' {f | f.χ = χ}) =
      cuspFormsNew N k ⊓ cuspFormCharSpace k χ := by
  refine le_antisymm (Submodule.span_le.mpr ?_) fun w hw ↦ ?_
  · rintro _ ⟨f, rfl, rfl⟩
    exact ⟨f.isNew, f.mem_charSpace⟩
  -- a basis of `S_k(N, χ)` of good Hecke eigenforms, each split into its old and new parts
  obtain ⟨I, b, hI, -, -, hb⟩ := exists_peterssonOrthonormalBasis_eigenformAwayFromLevel k χ
  have : Fintype I := Fintype.ofFinite I
  have hsplit (i : I) : ∃ o n : cuspFormCharSpace k χ,
      (o : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsOld N k ∧
        (n : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈ cuspFormsNew N k ∧ o + n = b i := by
    have hbi : ((b i : cuspFormCharSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
        cuspFormsOld N k ⊓ cuspFormCharSpace k χ ⊔ cuspFormsNew N k ⊓ cuspFormCharSpace k χ := by
      rw [sup_cuspFormsOld_cuspFormsNew_inf_cuspFormCharSpace]
      exact (b i).2
    obtain ⟨o, ho, n, hn, hon⟩ := Submodule.mem_sup.mp hbi
    exact ⟨⟨o, ho.2⟩, ⟨n, hn.2⟩, ho.1, hn.1, Subtype.ext hon⟩
  choose o n ho hn hon using hsplit
  -- each new part lies in the span of the newforms
  have hnspan (i : I) : ((n i : cuspFormCharSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) ∈
      Submodule.span ℂ ((fun f : Newform N k ↦ f.toCuspForm) '' {f | f.χ = χ}) := by
    obtain ⟨f, hfχ, hfb⟩ := hb i
    exact mem_span_of_forall_prime (hn i) fun p hp hpN ↦
      ⟨_, heckeRingHomCuspCharSpace_eq_smul_of_add_eq hp hpN (ho i) (hn i) (hon i)
        (EigenformAwayFromLevel.heckeRingHomCuspCharSpace_heckeTGeneratorGamma0_eq_smul hfχ hfb
          hp hpN)⟩
  -- `w` is the same combination of the new parts as it is of the basis vectors
  set W : cuspFormCharSpace k χ := ⟨w, hw.2⟩
  set v : cuspFormCharSpace k χ := ∑ i, b.repr W i • n i
  have hWv : W - v = ∑ i, b.repr W i • o i := by
    conv_lhs => rw [← b.sum_repr W]
    simp only [v, ← hon, smul_add, Finset.sum_add_distrib, add_sub_cancel_right]
  have hWv0 := (Submodule.disjoint_def.mp (disjoint_cuspFormsOld_cuspFormsNew N k))
    ((W - v : cuspFormCharSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k)
    (by
      rw [hWv, Submodule.coe_sum]
      exact Submodule.sum_mem _ fun i _ ↦ by
        rw [Submodule.coe_smul]
        exact Submodule.smul_mem _ _ (ho i))
    (by
      rw [Submodule.coe_sub, Submodule.coe_sum]
      exact Submodule.sub_mem _ hw.1 (Submodule.sum_mem _ fun i _ ↦ by
        rw [Submodule.coe_smul]
        exact Submodule.smul_mem _ _ (hn i)))
  have hwv : w = ((v : cuspFormCharSpace k χ) : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) :=
    congrArg Subtype.val (sub_eq_zero.mp (Submodule.coe_eq_zero.mp hWv0))
  rw [hwv, Submodule.coe_sum]
  exact Submodule.sum_mem _ fun i _ ↦ by
    rw [Submodule.coe_smul]
    exact Submodule.smul_mem _ _ (hnspan i)

/-- **The newforms span the new subspace**: the span of the underlying cusp forms of the newforms
of level `N` and weight `k` is `S_k(Γ₁(N))ⁿᵉʷ`. -/
theorem span_range_toCuspForm_eq_cuspFormsNew :
    Submodule.span ℂ (Set.range fun f : Newform N k ↦ f.toCuspForm) = cuspFormsNew N k := by
  refine le_antisymm (Submodule.span_le.mpr (Set.range_subset_iff.mpr fun f ↦ f.isNew)) ?_
  rw [← iSup_inf_cuspFormsNew_cuspFormCharSpace N k]
  exact iSup_le fun χ ↦ (span_image_toCuspForm_eq_cuspFormsNew_inf_cuspFormCharSpace χ).ge.trans
    (Submodule.span_mono (Set.image_subset_range _ _))

/-! ### The basis -/

variable (N k) in
/-- **The newforms, as a basis of the new subspace** `S_k(Γ₁(N))ⁿᵉʷ` (Miyake, Theorem 4.6.13(2);
Diamond–Shurman, Theorem 5.8.2). It is Petersson-orthogonal:
`Newform.peterssonInnerCosets_eq_zero_of_ne`. -/
noncomputable def basis : Module.Basis (Newform N k) ℂ (cuspFormsNew N k) :=
  (Module.Basis.span linearIndependent_toCuspForm).map
    (LinearEquiv.ofEq _ _ span_range_toCuspForm_eq_cuspFormsNew)

/-- The basis vector of `Newform.basis` at a newform is that newform. -/
@[simp]
theorem coe_basis_apply (f : Newform N k) :
    (basis N k f : CuspForm ((Gamma1 N).map (mapGL ℝ)) k) = f.toCuspForm := by
  simp [basis]

/-- There are finitely many newforms of a given level and weight. -/
instance : Finite (Newform N k) :=
  Module.Finite.finite_basis (basis N k)

end Newform

end HeckeRing.GL2

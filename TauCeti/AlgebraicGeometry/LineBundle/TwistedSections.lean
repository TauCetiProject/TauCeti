/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.NonvanishingLocus
public import TauCeti.AlgebraicGeometry.Modules.Localization
public import TauCeti.AlgebraicGeometry.Modules.Tensor.Sections
public import TauCeti.Algebra.Group.Action.Pow

/-!
# Sections of a module twisted by powers of a line bundle

Let `F` be an `𝒪_X`-module and `L` an `𝒪_X`-module with a section `e` over an open `U`. The maps
`t ↦ t ⊗ eⁿ` from `Γ(F, U)` to `Γ(F ⊗ Lⁿ, U)` (`Scheme.Modules.tmulRight` and
`Scheme.Modules.tensorPowSection`, in `TauCeti/AlgebraicGeometry/Modules/Tensor/Sections.lean`)
are bijective when `e` is a basis of `L` over `U`, for instance if `L` is an invertible sheaf and
`U` lies in the nonvanishing locus of `e`.

For a quasi-coherent `F` and an invertible `L`, this describes the sections of `F` over the
nonvanishing locus `X_s` of a section `s` of `L` over a quasi-compact quasi-separated open `U`
(Hartshorne, Lemma II.5.14; Stacks, Tag 01PW):

* a section `t` of `F` over `U` that vanishes on `X_s` satisfies `t ⊗ sⁿ = 0` for some `n`;
* for every section `t` of `F` over `X_s`, some `t ⊗ sⁿ` extends to a section of `F ⊗ Lⁿ` over
  `U`.

Together with the bijectivity of `t ↦ t ⊗ sⁿ` over `X_s`, these two statements express that
`Γ(X_s, F)` is the colimit of the modules `Γ(U, F ⊗ Lⁿ)` along `t ↦ t ⊗ s`; the colimit itself is
not constructed here. For the structure sheaf in place of `L` this is the localization
`Γ(X_f, F) = Γ(U, F)_f`
(`AlgebraicGeometry.Scheme.Modules.isLocalizedModule_basicOpenRestrict_of_qcqs`). It is the step
in the proof of Serre's theorem that a coherent sheaf becomes globally generated after twisting by
a high power of an ample line bundle: on projective space, sections of `F` over the standard opens
`D₊(xᵢ)` extend to global sections of the twists `F(n)` after multiplication by `xᵢⁿ`.

## Main results

* `AlgebraicGeometry.Scheme.Modules.bijective_tmulRight_tensorPowSection_of_le_nonvanishingLocus`:
  for an invertible sheaf `L`, `t ↦ t ⊗ eⁿ` is bijective over the nonvanishing locus of `e`.
* `AlgebraicGeometry.Scheme.Modules.exists_tmulRight_tensorPowSection_eq_zero`: a section over a
  quasi-compact open vanishing on `X_s` is killed by tensoring with a power of `s`.
* `AlgebraicGeometry.Scheme.Modules.exists_map_eq_tmulRight_tensorPowSection`: on a quasi-compact
  quasi-separated open, `t ⊗ sⁿ` extends from `X_s` for every section `t` over `X_s` and large `n`.

## References

* R. Hartshorne, *Algebraic Geometry*, GTM 52, Springer, 1977, Lemma II.5.14.
* [The Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW).
-/

public section

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite TopologicalSpace TauCeti

namespace AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {X : Scheme.{u}} (F : X.Modules) {L : X.Modules}

/-! ### Sections over the nonvanishing locus of a section of a line bundle -/

variable [TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible X L]

/-- For an invertible sheaf `L` and a section `e` of `L` over `U` that vanishes nowhere on `U`,
tensoring with `eⁿ` is a bijection `Γ(F, U) → Γ(F ⊗ Lⁿ, U)` for every `n`. -/
theorem bijective_tmulRight_tensorPowSection_of_le_nonvanishingLocus {U : X.Opens}
    (e : Γ(L, U)) (h : U ≤ L.nonvanishingLocus e) (n : ℕ) :
    Function.Bijective (tmulRight F (tensorPowSection e n)) :=
  bijective_tmulRight_tensorPowSection F e (fun W i ↦ by
    simpa only [Category.comp_id] using (le_nonvanishingLocus_iff e (𝟙 U)).mp h W i) n

/-- A quasi-compact open `U` is covered by finitely many affine opens `V i ≤ U`, each carrying a
section `e i` of `L` that vanishes nowhere on `V i`. -/
private theorem exists_finite_affine_cover_le_nonvanishingLocus {U : X.Opens}
    (hU : IsCompact (U : Set X)) :
    ∃ (ι : Type u) (_ : Finite ι) (V : ι → X.Opens) (e : ∀ i, Γ(L, V i)),
      (∀ i, IsAffineOpen (V i)) ∧ (∀ i, V i ≤ U) ∧ (∀ i, V i ≤ L.nonvanishingLocus (e i)) ∧
        U ≤ ⨆ i, V i := by
  -- Near each point of `U`, take an affine open inside `U` and inside a trivializing open.
  have H (x : U) : ∃ (A : X.Opens) (e : Γ(L, A)), IsAffineOpen A ∧ (x : X) ∈ A ∧ A ≤ U ∧
      A ≤ L.nonvanishingLocus e := by
    obtain ⟨V, t, hxV⟩ := exists_mem_trivialization L x
    obtain ⟨_, ⟨A, hA, rfl⟩, hxA, hAUV⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show (x : X) ∈ ((U ⊓ V : X.Opens) : Set X) from ⟨x.2, hxV⟩) (U ⊓ V).isOpen
    have hAV : A ≤ V := fun y hy ↦ (hAUV hy).2
    refine ⟨A, L.presheaf.map (homOfLE hAV).op (trivializationGenerator L t), hA, hxA,
      fun y hy ↦ (hAUV hy).1, ?_⟩
    rw [nonvanishingLocus_map, nonvanishingLocus_trivializationGenerator]
    exact le_inf le_rfl hAV
  choose A e hA hxA hAU hAe using H
  obtain ⟨t, ht⟩ := hU.elim_finite_subcover (fun x : U ↦ (A x : Set X)) (fun x ↦ (A x).isOpen)
    fun x hx ↦ Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxA ⟨x, hx⟩⟩
  refine ⟨t, inferInstance, fun i ↦ A i, fun i ↦ e i, fun i ↦ hA i, fun i ↦ hAU i,
    fun i ↦ hAe i, fun x hx ↦ ?_⟩
  obtain ⟨i, hi, hxi⟩ := Set.mem_iUnion₂.mp (ht hx)
  exact Opens.mem_iSup.mpr ⟨⟨i, hi⟩, hxi⟩

/-- If `e` vanishes nowhere on `V ≤ U` and `s|_V = f • e`, then `X_s ∩ V` is the basic open set
of `f`. -/
private theorem basicOpen_eq_inf_nonvanishingLocus {U V : X.Opens} (i : V ⟶ U) (s : Γ(L, U))
    {e : Γ(L, V)} (he : V ≤ L.nonvanishingLocus e) {f : Γ(X, V)}
    (hf : f • e = L.presheaf.map i.op s) : X.basicOpen f = V ⊓ L.nonvanishingLocus s := by
  rw [← inf_eq_left.mpr ((X.basicOpen_le f).trans he), ← nonvanishingLocus_smul, hf,
    nonvanishingLocus_map]

/-- **Sections vanishing on the nonvanishing locus are killed by a power of the section**
(Hartshorne, Lemma II.5.14(a)). Let `F` be quasi-coherent and `L` invertible, let `s` be a section
of `L` over a quasi-compact open `U`, and let `t` be a section of `F` over `U` that vanishes on the
nonvanishing locus `X_s`. Then `t ⊗ sⁿ = 0` in `Γ(F ⊗ Lⁿ, U)` for some `n`. -/
theorem exists_tmulRight_tensorPowSection_eq_zero [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (s : Γ(L, U)) (t : Γ(F, U))
    (ht : F.presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op t = 0) :
    ∃ n : ℕ, tmulRight F (tensorPowSection s n) t = 0 := by
  obtain ⟨ι, _, V, e, hVa, hVU, hVe, hUV⟩ :=
    exists_finite_affine_cover_le_nonvanishingLocus (L := L) hU
  cases nonempty_fintype ι
  -- On each `V i`, write `s = f i • e i`; then `X_s ∩ V i` is the basic open set of `f i`.
  choose f hf using fun i ↦
    surjective_smul_of_le_nonvanishingLocus (hVe i) (L.presheaf.map (homOfLE (hVU i)).op s)
  beta_reduce at hf
  have hD (i : ι) : X.basicOpen (f i) ≤ L.nonvanishingLocus s :=
    (basicOpen_eq_inf_nonvanishingLocus _ s (hVe i) (hf i)).le.trans inf_le_right
  -- So the restriction of `t` to `V i` is killed by a power of `f i`.
  have H (i : ι) : ∃ n : ℕ, f i ^ n • F.presheaf.map (homOfLE (hVU i)).op t = 0 := by
    refine F.exists_pow_smul_eq_zero_of_isCompact (hVa i).isCompact _ _ ?_
    rw [basicOpenRestrict_apply]
    simpa only [map_zero, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp] using
      congrArg (F.presheaf.map (homOfLE (hD i)).op) ht
  choose n hn using H
  refine ⟨Finset.univ.sup n, TopCat.Sheaf.eq_of_locally_eq'
    (⟨(F ⊗ tensorPow L _).presheaf, (F ⊗ tensorPow L _).isSheaf⟩ : TopCat.Sheaf AddCommGrpCat X)
    V U (fun i ↦ homOfLE (hVU i)) hUV _ _ fun i ↦ ?_⟩
  -- The restriction maps of this sheaf are those of `F ⊗ Lⁿ`.
  change (F ⊗ tensorPow L _).presheaf.map _ _ = (F ⊗ tensorPow L _).presheaf.map _ _
  rw [map_zero, map_tmulRight_tensorPowSection, ← hf i, tmulRight_tensorPowSection_smul,
    pow_smul_eq_zero_of_le (Finset.le_sup (f := n) (Finset.mem_univ i)) (hn i), map_zero]

/-- **Sections over the nonvanishing locus extend after tensoring with a power of the section**
(Hartshorne, Lemma II.5.14(b)). Let `F` be quasi-coherent and `L` invertible, and let `s` be a
section of `L` over a quasi-compact quasi-separated open `U`. For every section `t` of `F` over the
nonvanishing locus `X_s`, there are `n` and a section of `F ⊗ Lⁿ` over `U` whose restriction to
`X_s` is `t ⊗ sⁿ`. -/
theorem exists_map_eq_tmulRight_tensorPowSection [F.IsQuasicoherent] {U : X.Opens}
    (hU : IsCompact (U : Set X)) (hU' : IsQuasiSeparated (U : Set X)) (s : Γ(L, U))
    (t : Γ(F, L.nonvanishingLocus s)) :
    ∃ (n : ℕ) (t' : Γ(F ⊗ tensorPow L n, U)),
      (F ⊗ tensorPow L n).presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op t' =
        tmulRight F
          (tensorPowSection (L.presheaf.map (homOfLE (L.nonvanishingLocus_le s)).op s) n) t := by
  obtain ⟨ι, _, V, e, hVa, hVU, hVe, hUV⟩ :=
    exists_finite_affine_cover_le_nonvanishingLocus (L := L) hU
  cases nonempty_fintype ι
  -- On each `V i`, write `s = f i • e i`; then `X_s ∩ V i` is the basic open set of `f i`.
  choose f hf using fun i ↦
    surjective_smul_of_le_nonvanishingLocus (hVe i) (L.presheaf.map (homOfLE (hVU i)).op s)
  beta_reduce at hf
  have hDf (i : ι) : X.basicOpen (f i) = V i ⊓ L.nonvanishingLocus s :=
    basicOpen_eq_inf_nonvanishingLocus _ s (hVe i) (hf i)
  have hfD (i : ι) : X.basicOpen (f i) ≤ L.nonvanishingLocus s := (hDf i).le.trans inf_le_right
  -- On each affine `V i`, a common power `f i ^ N • t` extends to a section `y' i` over `V i`.
  obtain ⟨N, y', hy'⟩ := exists_pow_smul_eq_map_of_finite F hVa f hfD t
  -- On an overlap `V i ⊓ V j`, the basis sections differ by a function `u`, `e i = u • e j`, and
  -- then `f j = u * f i`.
  have hW (i j : ι) : V i ⊓ V j ≤ L.nonvanishingLocus
      (L.presheaf.map (homOfLE (inf_le_right : V i ⊓ V j ≤ V j)).op (e j)) := by
    rw [nonvanishingLocus_map]
    exact le_inf le_rfl (inf_le_right.trans (hVe j))
  choose u hu using fun p : ι × ι ↦ surjective_smul_of_le_nonvanishingLocus (hW p.1 p.2)
    (L.presheaf.map (homOfLE (inf_le_left : V p.1 ⊓ V p.2 ≤ V p.1)).op (e p.1))
  beta_reduce at hu
  have hs (j : ι) {W : X.Opens} (k : W ⟶ V j) :
      X.presheaf.map k.op (f j) • L.presheaf.map k.op (e j) =
        L.presheaf.map (homOfLE (k.le.trans (hVU j))).op s := by
    rw [← L.map_smul, hf, ← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
    rfl
  have hfu (p : ι × ι) : X.presheaf.map (homOfLE inf_le_right).op (f p.2) =
      u p * X.presheaf.map (homOfLE inf_le_left).op (f p.1) := by
    apply injective_smul_of_le_nonvanishingLocus (hW p.1 p.2)
    beta_reduce
    rw [hs p.2, mul_comm, mul_smul, hu p, hs p.1]
  -- After transport to `e j`, the extensions `y' i` and `y' j` agree on `V i ⊓ V j ∩ X_s`, so
  -- they agree on `V i ⊓ V j` after multiplication by a power of `f j`.
  have hδ (p : ι × ι) := exists_pow_smul_sub_eq_zero F
    (hU' _ _ (hVU p.1) (V p.1).isOpen (hVa p.1).isCompact (hVU p.2) (V p.2).isOpen
      (hVa p.2).isCompact) (hDf p.1) (hDf p.2) (hfu p) (hy' p.1) (hy' p.2)
  choose m hm using hδ
  let M := Finset.univ.sup m
  let y'' (i : ι) : Γ(F, V i) := f i ^ M • y' i
  -- The sections `y'' i ⊗ (e i)^(N + M)` are compatible, so they glue to a section over `U`.
  let z (i : ι) : Γ(F ⊗ tensorPow L (N + M), V i) :=
    tmulRight F (tensorPowSection (e i) (N + M)) (y'' i)
  have hc : TopCat.Presheaf.IsCompatible (F ⊗ tensorPow L (N + M)).presheaf V z := by
    intro i j
    have h := pow_smul_eq_zero_of_le (Finset.le_sup (f := m) (Finset.mem_univ (i, j)))
      (hm (i, j))
    rw [smul_sub, sub_eq_zero] at h
    -- The inclusions of `V i ⊓ V j` in `V i` and `V j` are `homOfLE`.
    change (F ⊗ tensorPow L (N + M)).presheaf.map (homOfLE inf_le_left).op _ =
      (F ⊗ tensorPow L (N + M)).presheaf.map (homOfLE inf_le_right).op _
    simp only [z, map_tmulRight_tensorPowSection]
    rw [← hu (i, j), tmulRight_tensorPowSection_smul]
    congr 1
    simp only [y'', F.map_smul, map_pow]
    rw [← h, hfu (i, j), smul_smul, smul_smul]
    congr 1
    ring
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing'
    (⟨(F ⊗ tensorPow L (N + M)).presheaf, (F ⊗ tensorPow L (N + M)).isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat X) V U (fun i ↦ homOfLE (hVU i)) hUV z hc
  -- On each `X_s ∩ V i`, both sections restrict to `t ⊗ s^(N + M)`.
  refine ⟨N + M, g, TopCat.Sheaf.eq_of_locally_eq'
    (⟨(F ⊗ tensorPow L (N + M)).presheaf, (F ⊗ tensorPow L (N + M)).isSheaf⟩ :
      TopCat.Sheaf AddCommGrpCat X) (fun i ↦ X.basicOpen (f i)) _ (fun i ↦ homOfLE (hfD i))
    (fun x hx ↦ ?_) _ _ fun i ↦ ?_⟩
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hUV (L.nonvanishingLocus_le s hx))
    exact Opens.mem_iSup.mpr ⟨i, (hDf i).ge ⟨hi, hx⟩⟩
  -- The restriction maps of this sheaf are those of `F ⊗ L^(N + M)`.
  change (F ⊗ tensorPow L (N + M)).presheaf.map _ _ = (F ⊗ tensorPow L (N + M)).presheaf.map _ _
  have hg' := congrArg ((F ⊗ tensorPow L (N + M)).presheaf.map
    (homOfLE (X.basicOpen_le (f i))).op) (hg i)
  simp only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp] at hg'
  rw [← Functor.map_comp_apply, ← op_comp, homOfLE_comp, hg', map_tmulRight_tensorPowSection,
    map_tmulRight_tensorPowSection]
  simp only [y'', F.map_smul, map_pow, hy', smul_smul, ← pow_add]
  rw [add_comm M N, ← tmulRight_tensorPowSection_smul, hs i]
  simp only [← Functor.map_comp_apply, ← op_comp, homOfLE_comp]

end

end AlgebraicGeometry.Scheme.Modules

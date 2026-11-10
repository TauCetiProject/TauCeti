/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.Glue
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.CategoryTheory.ObjectProperty.Shift

/-!
# Acyclic complexes over an exact category

A cochain complex `K` over an exact category is **acyclic** when each differential factors as a
deflation followed by an inflation, `Kⁿ ↠ Zⁿ⁺¹ ↣ Kⁿ⁺¹`, such that every sequence
`Zⁿ ↣ Kⁿ ↠ Zⁿ⁺¹` is a conflation (Bühler, Definition 10.1). For the abelian exact structure these
are the exact complexes. Acyclic complexes are the complexes inverted to zero in the derived
category of an exact category.

The acyclic complexes contain zero and are closed under isomorphisms of complexes, shifts and
direct sums. The main result is **Neeman's lemma**: the mapping cone of a chain map `φ : K ⟶ L`
between acyclic complexes is acyclic. Write `ZₙK ↣ Kⁿ` and `ZₙL ↣ Lⁿ` for the cycles; `φ` restricts
to `gₙ : ZₙK ⟶ ZₙL`. The cycles `Wₙ` of the cone are the pushouts of `ZₙK ↣ Kⁿ` along `gₙ`, which
are extensions of `Zₙ₊₁K` by `ZₙL`, and gluing the pullback square at `n` with the pushout square
at `n + 1` (`TauCeti.ExactStructure.conflation_shortComplex'_of_isPullback_of_isPushout`) gives the
conflations `Wₙ ↣ Kⁿ⁺¹ ⊞ Lⁿ ↠ Wₙ₊₁` of the cone.

## Main definitions

* `TauCeti.ExactStructure.AcyclicData`: a factorization of the differentials of a complex
  through conflations.
* `TauCeti.ExactStructure.acyclic`: the acyclic complexes of an exact structure, characterized by
  `TauCeti.ExactStructure.acyclic_iff`.

## Main results

* `TauCeti.ExactStructure.acyclic_biprod`, and instances for isomorphisms, shifts and zero.
* `TauCeti.ExactStructure.acyclic_mappingCone`: **Neeman's lemma**, the mapping cone of a chain
  map between acyclic complexes is acyclic.

## References

* Theo Bühler, *Exact categories*, Expositiones Mathematicae **28** (2010), 1--69,
  <https://arxiv.org/abs/0811.1480>, Definition 10.1 and Lemma 10.3.
* Amnon Neeman, *The derived category of an exact category*, J. Algebra **135** (1990),
  388--394, Lemma 1.1.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits ZeroObject

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C] [HasBinaryBiproducts C]

namespace ExactStructure

variable (E : ExactStructure C)

/-- A witness that a cochain complex `K` is acyclic for an exact structure `E`: objects `Z n` and
a factorization `K.X n ↠ Z (n + 1) ↣ K.X (n + 1)` of each differential such that every
`Z n ↣ K.X n ↠ Z (n + 1)` is a conflation. -/
structure AcyclicData (K : CochainComplex C ℤ) where
  /-- The objects of cycles. -/
  Z : ℤ → C
  /-- The inflation of the cycles into the complex. -/
  i (n : ℤ) : Z n ⟶ K.X n
  /-- The deflation onto the next cycles. -/
  p (n : ℤ) : K.X n ⟶ Z (n + 1)
  zero (n : ℤ) : i n ≫ p n = 0
  conflation (n : ℤ) : E.Conflation (ShortComplex.mk (i n) (p n) (zero n))
  fac (n : ℤ) : p n ≫ i (n + 1) = K.d n (n + 1)

/-- A cochain complex is **acyclic** for an exact structure `E` when each differential factors as
a deflation followed by an inflation, `K.X n ↠ Z (n + 1) ↣ K.X (n + 1)`, such that every sequence
`Z n ↣ K.X n ↠ Z (n + 1)` is a conflation. -/
def acyclic : ObjectProperty (CochainComplex C ℤ) := fun K ↦ Nonempty (E.AcyclicData K)

/-- A complex is acyclic exactly when it has acyclicity data. -/
theorem acyclic_iff (K : CochainComplex C ℤ) : E.acyclic K ↔ Nonempty (E.AcyclicData K) :=
  Iff.rfl

variable {E} in
/-- Acyclicity data make a complex acyclic. -/
theorem AcyclicData.acyclic {K : CochainComplex C ℤ} (h : E.AcyclicData K) : E.acyclic K :=
  ⟨h⟩

namespace AcyclicData

variable {E}

/-- Acyclicity data for a complex all of whose terms are zero. -/
noncomputable def ofIsZero {K : CochainComplex C ℤ} (hK : ∀ n, IsZero (K.X n)) :
    E.AcyclicData K where
  Z _ := 0
  i _ := 0
  p _ := 0
  zero _ := by simp
  conflation n := E.conflation_of_splitting
    (ShortComplex.Splitting.ofIsIsoOfIsZero _ (isIso_of_source_target_iso_zero _
      (isZero_zero C).isoZero ((hK n).isoZero)) (isZero_zero C))
  fac n := (hK n).eq_of_src _ _

/-- Acyclicity data transported along an isomorphism of complexes. -/
def ofIso {K L : CochainComplex C ℤ} (h : E.AcyclicData K) (e : K ≅ L) : E.AcyclicData L where
  Z := h.Z
  i n := h.i n ≫ (HomologicalComplex.Hom.isoApp e n).hom
  p n := (HomologicalComplex.Hom.isoApp e n).inv ≫ h.p n
  zero n := by rw [Category.assoc, Iso.hom_inv_id_assoc, h.zero]
  conflation n := E.conflation_of_iso (S := ShortComplex.mk _ _ (h.zero n))
    (ShortComplex.isoMk (Iso.refl _) (HomologicalComplex.Hom.isoApp e n) (Iso.refl _)
      (by simp) (by simp [← HomologicalComplex.comp_f_assoc])) (h.conflation n)
  fac n := by simp [reassoc_of% (h.fac n), ← HomologicalComplex.comp_f]

/-- Acyclicity data for a direct sum of two complexes. -/
noncomputable def biprod {K L : CochainComplex C ℤ} (h : E.AcyclicData K) (h' : E.AcyclicData L) :
    E.AcyclicData (K ⊞ L) where
  Z n := h.Z n ⊞ h'.Z n
  i n := Limits.biprod.desc (h.i n ≫ (Limits.biprod.inl : K ⟶ K ⊞ L).f n)
    (h'.i n ≫ (Limits.biprod.inr : L ⟶ K ⊞ L).f n)
  p n := Limits.biprod.lift ((Limits.biprod.fst : K ⊞ L ⟶ K).f n ≫ h.p n)
    ((Limits.biprod.snd : K ⊞ L ⟶ L).f n ≫ h'.p n)
  zero n := by ext <;> simp [h.zero, h'.zero]
  conflation n := by
    let S := ShortComplex.mk (Limits.biprod.map (h.i n) (h'.i n))
      (Limits.biprod.map (h.p n) (h'.p n)) (by ext <;> simp [h.zero, h'.zero])
    have hS : E.Conflation S := E.conflation_biprod (h.conflation n) (h'.conflation n)
    refine E.conflation_of_iso (S := S) (ShortComplex.isoMk (Iso.refl _)
      (HomologicalComplex.biprodXIso K L n).symm (Iso.refl _) ?_ ?_) hS
    · ext <;> simp [S]
    · ext <;> simp [S]
  fac n := by
    ext
    · simp [h.fac]
    · simp
    · simp
    · simp [h'.fac]

/-- Acyclicity data for a shift of a complex: the cycles are shifted, and the deflations pick up
the sign of the shifted differential. -/
noncomputable def shift {K : CochainComplex C ℤ} (h : E.AcyclicData K) (a : ℤ) :
    E.AcyclicData (K⟦a⟧) where
  Z n := h.Z (n + a)
  i n := h.i (n + a)
  p n := a.negOnePow • (h.p (n + a) ≫ eqToHom (congrArg h.Z (by lia)))
  zero n := by simp [reassoc_of% (h.zero (n + a))]
  conflation n := by
    let e : h.Z (n + a + 1) ≅ h.Z (n + 1 + a) :=
      { hom := a.negOnePow • eqToHom (congrArg h.Z (by lia))
        inv := a.negOnePow • eqToHom (congrArg h.Z (by lia))
        hom_inv_id := by simp [smul_smul]
        inv_hom_id := by simp [smul_smul] }
    refine E.conflation_of_iso (S := ShortComplex.mk _ _ (h.zero (n + a)))
      (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) e (by simp) (by simp [e])) (h.conflation _)
  fac n := by
    have key (m m' : ℤ) (hm : m = m') :
        eqToHom (congrArg h.Z hm) ≫ h.i m' = h.i m ≫ eqToHom (congrArg K.X hm) := by
      subst hm; simp
    have key' (j j' : ℤ) (hj : j = j') :
        K.d (n + a) j ≫ eqToHom (congrArg K.X hj) = K.d (n + a) j' := by
      subst hj; simp
    rw [CochainComplex.shiftFunctor_obj_d', Units.smul_def, Units.smul_def, Preadditive.zsmul_comp,
      Category.assoc, key (n + a + 1) (n + 1 + a) (by lia), reassoc_of% (h.fac (n + a)),
      key' _ _ (by lia)]

section descZ

variable {K : CochainComplex C ℤ} (h : E.AcyclicData K)

/-- The morphism out of the cycles `Zⁿ⁺¹` induced by a morphism out of `Kⁿ` killing `Zⁿ ↣ Kⁿ`. -/
noncomputable def descZ {T : C} (n : ℤ) (k : K.X n ⟶ T) (hk : h.i n ≫ k = 0) : h.Z (n + 1) ⟶ T :=
  (E.isKernelCokernelPair _ (h.conflation n)).desc k hk

@[reassoc (attr := simp)]
theorem p_descZ {T : C} (n : ℤ) (k : K.X n ⟶ T) (hk : h.i n ≫ k = 0) :
    h.p n ≫ h.descZ n k hk = k :=
  (E.isKernelCokernelPair _ (h.conflation n)).g_desc k hk

instance (n : ℤ) : Epi (h.p n) := (E.isDeflation_g (h.conflation n)).epi

end descZ

end AcyclicData

/-- An acyclic complex stays acyclic under isomorphism of complexes. -/
instance : E.acyclic.IsClosedUnderIsomorphisms where
  of_iso e := fun ⟨h⟩ ↦ ⟨h.ofIso e⟩

/-- The zero complex is acyclic. -/
instance : E.acyclic.ContainsZero where
  exists_zero := ⟨HomologicalComplex.zero, HomologicalComplex.isZero_zero,
    ⟨AcyclicData.ofIsZero fun _ ↦ isZero_zero C⟩⟩

/-- A shift of an acyclic complex is acyclic. -/
instance : E.acyclic.IsStableUnderShift ℤ where
  isStableUnderShiftBy a := ⟨fun _ ⟨h⟩ ↦ ⟨h.shift a⟩⟩

/-- A direct sum of acyclic complexes is acyclic. -/
theorem acyclic_biprod {K L : CochainComplex C ℤ} (hK : E.acyclic K) (hL : E.acyclic L) :
    E.acyclic (K ⊞ L) :=
  let ⟨h⟩ := hK
  let ⟨h'⟩ := hL
  ⟨h.biprod h'⟩

/-- **Neeman's lemma**: the mapping cone of a chain map between acyclic complexes is acyclic
(Bühler, Lemma 10.3). -/
theorem acyclic_mappingCone {K L : CochainComplex C ℤ} (φ : K ⟶ L) (hK : E.acyclic K)
    (hL : E.acyclic L) : E.acyclic (CochainComplex.mappingCone φ) := by
  open CochainComplex.mappingCone in
  obtain ⟨A⟩ := hK
  obtain ⟨B⟩ := hL
  have hA (n : ℤ) := E.isKernelCokernelPair _ (A.conflation n)
  have hB (n : ℤ) := E.isKernelCokernelPair _ (B.conflation n)
  -- The chain map restricts to the cycles.
  have hz (n : ℤ) : (A.i n ≫ φ.f n) ≫ B.p n = 0 := by
    have := (hB (n + 1)).mono_f
    rw [← cancel_mono (B.i (n + 1)), zero_comp]
    rw [Category.assoc, Category.assoc, B.fac, φ.comm, ← A.fac, Category.assoc,
      reassoc_of% (A.zero n), zero_comp]
  let g (n : ℤ) : A.Z n ⟶ B.Z n :=
    (KernelFork.IsLimit.lift' (hB n).fIsKernel (A.i n ≫ φ.f n) (hz n)).1
  have hg (n : ℤ) : g n ≫ B.i n = A.i n ≫ φ.f n :=
    (KernelFork.IsLimit.lift' (hB n).fIsKernel (A.i n ≫ φ.f n) (hz n)).2
  have hpg (n : ℤ) : A.p n ≫ g (n + 1) = φ.f n ≫ B.p n := by
    have := (hB (n + 1)).mono_f
    rw [← cancel_mono (B.i (n + 1)), Category.assoc, hg, ← Category.assoc, A.fac, Category.assoc,
      B.fac, φ.comm]
  -- The pushouts `Wₙ` of `Aᵢ` along `g`, the cycles of the cone.
  have (n : ℤ) : HasPushout (A.i n) (g n) :=
    E.hasPushouts_inflations.hasPushout (g n) (E.isInflation_f (A.conflation n))
  let W (n : ℤ) := pushout (A.i n) (g n)
  have sq (n : ℤ) : IsPushout (A.i n) (g n) (pushout.inl _ _ : K.X n ⟶ W n)
      (pushout.inr _ _ : B.Z n ⟶ W n) := IsPushout.of_hasPushout _ _
  let e (n : ℤ) : W n ⟶ A.Z (n + 1) := cobaseChangeπ (ShortComplex.mk _ _ (A.zero n)) (sq n)
  have hue (n : ℤ) : pushout.inl (A.i n) (g n) ≫ e n = A.p n :=
    inl_cobaseChangeπ (ShortComplex.mk _ _ (A.zero n)) (sq n)
  have hke (n : ℤ) : pushout.inr (A.i n) (g n) ≫ e n = 0 :=
    inr_cobaseChangeπ (ShortComplex.mk _ _ (A.zero n)) (sq n)
  have hke' (n : ℤ) : E.Conflation (ShortComplex.mk _ (e n) (hke n)) := by
    have := E.conflation_cobaseChange (A.conflation n) (sq n)
    rwa [cobaseChange_def] at this
  let v (n : ℤ) : W n ⟶ L.X n := (sq n).desc (φ.f n) (B.i n) (hg n).symm
  have huv (n : ℤ) : pushout.inl (A.i n) (g n) ≫ v n = φ.f n := (sq n).inl_desc _ _ _
  have hkv (n : ℤ) : pushout.inr (A.i n) (g n) ≫ v n = B.i n := (sq n).inr_desc _ _ _
  -- The left squares are pullbacks.
  have hl (n : ℤ) : IsPullback (e n) (v n) (g (n + 1)) (B.p n) := by
    let ψ : ShortComplex.mk _ (e n) (hke n) ⟶ ShortComplex.mk _ _ (B.zero n) :=
      { τ₁ := 𝟙 _
        τ₂ := v n
        τ₃ := g (n + 1)
        comm₁₂ := by simp [hkv]
        comm₂₃ := by
          apply (sq n).hom_ext
          · rw [reassoc_of% (hue n), hpg, reassoc_of% (huv n)]
          · rw [reassoc_of% (hke n), reassoc_of% (hkv n), B.zero, zero_comp] }
    exact (E.isPullback_of_conflation_of_isIso₁ ψ (hke' n) (B.conflation n)).flip
  -- Gluing the pullback at `m` with the pushout at `m + 1` (Bühler, Corollary 3.6).
  have hglue (m : ℤ) := E.conflation_shortComplex'_of_isPullback_of_isPushout (hl m) (sq (m + 1))
    (E.isDeflation_g (B.conflation m)) (E.isInflation_f (A.conflation (m + 1)))
  refine ⟨{
    Z := W
    i m := -(e m ≫ A.i (m + 1)) ≫ (inl φ).v (m + 1) m (by lia) + v m ≫ (inr φ).f m
    p m := (fst φ).1.v m (m + 1) rfl ≫ pushout.inl (A.i (m + 1)) (g (m + 1)) +
      (snd φ).v m m (add_zero m) ≫ B.p m ≫ pushout.inr (A.i (m + 1)) (g (m + 1))
    zero m := ?_
    conflation m := ?_
    fac m := ?_ }⟩
  · simp only [Preadditive.add_comp, Preadditive.comp_add, Preadditive.neg_comp, Category.assoc,
      inl_v_fst_v_assoc, inl_v_snd_v_assoc, inr_f_fst_v_assoc, inr_f_snd_v_assoc, zero_comp,
      comp_zero, add_zero]
    rw [(sq (m + 1)).w, ← Category.assoc (e m), (hl m).w, Category.assoc]
    simp
  · refine E.conflation_of_iso ?_ (hglue m)
    -- The two isomorphisms are given as anonymous structures, so their types are stated.
    exact ShortComplex.isoMk (Iso.refl _)
      (show K.X (m + 1) ⊞ L.X m ≅ (CochainComplex.mappingCone φ).X m from
      { hom := biprod.desc (-(inl φ).v (m + 1) m (by lia)) ((inr φ).f m)
        inv := biprod.lift (-(fst φ).1.v m (m + 1) rfl) ((snd φ).v m m (add_zero m))
        hom_inv_id := by apply biprod.hom_ext' <;> apply biprod.hom_ext <;> simp
        inv_hom_id := by simp [biprod.lift_desc, id_X φ m (m + 1) rfl] })
      (show W (m + 1) ≅ W (m + 1) from
      { hom := -𝟙 _
        inv := -𝟙 _
        hom_inv_id := by simp
        inv_hom_id := by simp })
      (by
        dsimp only [CommSq.shortComplex']
        apply ext_to φ m (m + 1) rfl <;> simp)
      (by
        dsimp only [CommSq.shortComplex']
        apply biprod.hom_ext' <;> simp [W])
  · apply ext_from φ (m + 1) m rfl <;> apply ext_to φ (m + 1) (m + 1 + 1) rfl
    · simp [d_fst_v φ m (m + 1) (m + 1 + 1) rfl rfl, reassoc_of% (hue (m + 1)), A.fac]
    · simp [d_snd_v φ m (m + 1) rfl, huv]
    · simp [reassoc_of% (hke (m + 1))]
    · simp [hkv, B.fac]

/-- **The mapping cone of a map built from pushouts of inflations is acyclic.** Let `φ : K ⟶ L`
come with objects `Bᵐ`, inflations `j : Bᵐ ↣ Lᵐ` and pushout squares
```text
Bᵐ ──j──▶ Lᵐ
│q        │u
▼         ▼
Kᵐ⁺¹ ─v─▶ Bᵐ⁺¹
```
such that the differential of `L` is `u ≫ j`, `φ` is `v ≫ j`, the differential of `K` is `v ≫ q`
and `u ≫ q = 0`. Then the cone of `φ` is acyclic, with cycles `Bᵐ`: the pushout conflations
`Bᵐ ↣ Lᵐ ⊞ Kᵐ⁺¹ ↠ Bᵐ⁺¹` are its degreewise conflations. This is the dual of the last step of
Bühler's proof of Theorem 12.7, where such data come from a recursive construction. -/
theorem acyclic_mappingCone_of_isPushout {K L : CochainComplex C ℤ} (φ : K ⟶ L) (B : ℤ → C)
    (j : ∀ m, B m ⟶ L.X m) (q : ∀ m, B m ⟶ K.X (m + 1)) (u : ∀ m, L.X m ⟶ B (m + 1))
    (v : ∀ m, K.X m ⟶ B m) (hj : ∀ m, E.IsInflation (j m))
    (sq : ∀ m, IsPushout (j m) (q m) (u m) (v (m + 1)))
    (hd : ∀ m, u m ≫ j (m + 1) = L.d m (m + 1)) (hφ : ∀ m, v m ≫ j m = φ.f m)
    (hq : ∀ m, v m ≫ q m = K.d m (m + 1)) (huq : ∀ m, u m ≫ q (m + 1) = 0) :
    E.acyclic (CochainComplex.mappingCone φ) := by
  open CochainComplex.mappingCone in
  refine ⟨{
    Z := B
    i m := j m ≫ (inr φ).f m - q m ≫ (inl φ).v (m + 1) m (by lia)
    p m := (fst φ).1.v m (m + 1) rfl ≫ v (m + 1) + (snd φ).v m m (add_zero m) ≫ u m
    zero m := by simp [(sq m).w]
    conflation m := ?_
    fac m := ?_ }⟩
  · refine E.conflation_of_iso ?_
      (E.conflation_shortComplex_of_isPushout_of_isInflation (hj m) (sq m))
    let e := biprod.braiding _ _ ≪≫
      (HomologicalComplex.homotopyCofiber.XIsoBiprod φ m (m + 1) rfl).symm
    -- The isomorphism `Lᵐ ⊞ Kᵐ⁺¹ ≅ cone` is the decomposition of the cone into its two summands.
    -- Mathlib's simp lemmas for `XIsoBiprod` carry their own biproduct instance, so they are
    -- applied by unification rather than by `simp`.
    have h₁ : biprod.inr ≫ (HomologicalComplex.homotopyCofiber.XIsoBiprod φ m (m + 1) rfl).inv =
        (inr φ).f m :=
      HomologicalComplex.homotopyCofiber.inr_XIsoBiprod_inv φ (m + 1) m rfl
    have h₂ : biprod.inl ≫ (HomologicalComplex.homotopyCofiber.XIsoBiprod φ m (m + 1) rfl).inv =
        (inl φ).v (m + 1) m (by lia) :=
      HomologicalComplex.homotopyCofiber.inl_XIsoBiprod_inv φ (m + 1) m rfl
    -- The last step of each case closes by unification, for the same reason.
    have he : e.hom = biprod.desc ((inr φ).f m) ((inl φ).v (m + 1) m (by lia)) := by
      apply biprod.hom_ext'
      · simp only [e, Iso.trans_hom, Iso.symm_hom, biprod.braiding_hom, biprod.lift_eq,
          Preadditive.add_comp, Category.assoc, h₁, Preadditive.comp_add,
          BinaryBicone.inl_snd_assoc, zero_comp, zero_add]
        exact (biprod.inl_fst_assoc _).trans (biprod.inl_desc _ _).symm
      · simp only [e, Iso.trans_hom, Iso.symm_hom, biprod.braiding_hom, biprod.lift_eq,
          Preadditive.add_comp, Category.assoc, h₂, Preadditive.comp_add,
          BinaryBicone.inr_fst_assoc, zero_comp, add_zero]
        exact (biprod.inr_snd_assoc _).trans (biprod.inr_desc _ _).symm
    refine ShortComplex.isoMk (Iso.refl _) e (Iso.refl _) ?_ ?_
    · dsimp only [CommSq.shortComplex]
      rw [he]
      apply ext_to φ m (m + 1) rfl <;> simp [sub_eq_add_neg]
    · dsimp only [CommSq.shortComplex]
      rw [he]
      apply biprod.hom_ext' <;> simp
  · apply ext_from φ (m + 1) m rfl <;> apply ext_to φ (m + 1) (m + 1 + 1) rfl
    · simp [d_fst_v φ m (m + 1) (m + 1 + 1) rfl rfl, reassoc_of% (hq (m + 1))]
    · simp [d_snd_v φ m (m + 1) rfl, hφ]
    · simp [huq]
    · simp [hd]

/-- Acyclicity of mapping cones is invariant under isomorphisms of arrows, through Mathlib's
`HomologicalComplex.homotopyCofiber.mapArrowIso`. -/
theorem acyclic_mappingCone_of_iso {K₁ L₁ K₂ L₂ : CochainComplex C ℤ} {φ₁ : K₁ ⟶ L₁}
    {φ₂ : K₂ ⟶ L₂} (a : K₁ ≅ K₂) (b : L₁ ≅ L₂) (comm : φ₁ ≫ b.hom = a.hom ≫ φ₂)
    (h : E.acyclic (CochainComplex.mappingCone φ₂)) :
    E.acyclic (CochainComplex.mappingCone φ₁) :=
  E.acyclic.prop_of_iso (HomologicalComplex.homotopyCofiber.mapArrowIso φ₂ φ₁
    (fun j ↦ ⟨j - 1, by simp⟩) (Arrow.isoMk a b comm.symm).symm) h

end ExactStructure

end TauCeti

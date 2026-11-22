/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.CochainComplexOpposite
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift
public import Mathlib.Tactic.Ring

/-!
# Regrading a chain complex as a cochain complex

For an integer `n`, a chain complex `K` indexed by `ℤ` (differential of degree `-1`) is regraded
into the cochain complex `C` with `C^k = K_(n-k)` and the *same* differential `d_C = d_K`, which
now has degree `+1`. This is the passage from homological to cohomological grading used for
Hamiltonian Floer complexes, where `C^k = CF_(n-k)` with `2n` the dimension of the symplectic
manifold: the pair-of-pants product `CF_i ⊗ CF_j → CF_(i+j-n)` becomes a product of degree zero
on `C`, and the Poincaré duality comparison `H^k → H_(2n-k) → FH_(n-k)` lands in `H^k(C)`.

The regrading is the restriction along the embedding of complex shapes `k ↦ n - k` from `up ℤ`
to `down ℤ`, and its inverse is the restriction along `k ↦ n - k` from `down ℤ` to `up ℤ`; in
particular `HomologicalComplex.restriction_d` computes the regraded differential as `d_K`.
The construction follows Mathlib's `ChainComplex.cochainComplexEquivalence`, which is the case
`k ↦ -k`, and for `n = 0` agrees with it up to this indexing convention. For general `n` the
regrading is not the composite of that equivalence with the shift `⟦-n⟧` of cochain complexes:
Mathlib's shift multiplies the differential by `(-1)^n`, whereas the regrading keeps the
differential. The two agree up to the sign-twisted isomorphism `ChainComplex.regradeIsoShift`,
whose component in degree `k` is `(-1)^(n k)`.

Both embeddings satisfy `IsTruncGE` and `IsTruncLE`, so homotopies and homotopy equivalences
regrade by `Homotopy.restriction` and `HomotopyEquiv.restriction`, and the homology in degree `k`
of the regraded complex is the homology of `K` in degree `n - k`.

## Main definitions and results

* `ComplexShape.embeddingUpIntDownIntSub`, `ComplexShape.embeddingDownIntUpIntSub`: the
  embeddings `k ↦ n - k` between the complex shapes `up ℤ` and `down ℤ`.
* `ChainComplex.regradeEquivalence`: the equivalence of categories
  `ChainComplex C ℤ ≌ CochainComplex C ℤ` given by `C^k = K_(n-k)` and `d_C = d_K`.
* `ChainComplex.regradeIsoOfEq`: the regradings by two equal integers `n = n'` are isomorphic,
  through the identifications `K_(n-k) = K_(n'-k)`.
* `ChainComplex.regradeHomologyIso`: the homology of the regraded complex in degree `k` is the
  homology of `K` in degree `n - k`, naturally in `K` (`regradeHomologyIso_hom_naturality`), and
  compatibly with the cycles and opcycles of both complexes.
* `ChainComplex.regradeIsoShift`: the regrading is isomorphic to the composite of Mathlib's
  `cochainComplexEquivalence` with the shift by `-n`, through the signs `(-1)^(n k)`
  (`regradeIsoShift_hom_app_f`, `regradeIsoShift_inv_app_f`).
* `CochainComplex.restrictionDownIntUpIntCyclesIso`,
  `CochainComplex.restrictionDownIntUpIntHomologyIso`: the cycles and homology in degree `i` of
  the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ` of Mathlib's `ChainComplex.cochainComplexEquivalence`
  are those of the cochain complex `K` in degree `-i`.

## References

* S. Piunikhin, D. Salamon, M. Schwarz, *Symplectic Floer–Donaldson theory and quantum
  cohomology*, Publ. Newton Inst. 8 (1996), for the cohomological regrading of Floer complexes.
-/

public section

open CategoryTheory Limits

namespace ComplexShape

/-- The embedding of the complex shape `up ℤ` in `down ℤ` given by `k ↦ n - k`. Its body is
exposed so that the regraded complex has `C^k = K_(n-k)` definitionally. -/
@[expose, simps]
def embeddingUpIntDownIntSub (n : ℤ) : (up ℤ).Embedding (down ℤ) where
  f k := n - k
  injective_f _ _ h := by simpa using h
  rel {i j} h := by simp only [up_Rel, down_Rel] at h ⊢; omega

instance (n : ℤ) : (embeddingUpIntDownIntSub n).IsTruncGE where
  rel' {i j} h := by simp only [up_Rel, down_Rel, embeddingUpIntDownIntSub_f] at h ⊢; omega
  mem_next {_ k'} _ := ⟨n - k', by simp⟩

instance (n : ℤ) : (embeddingUpIntDownIntSub n).IsTruncLE where
  mem_prev {i' _} _ := ⟨n - i', by simp⟩

/-- The embedding of the complex shape `down ℤ` in `up ℤ` given by `k ↦ n - k`. Its body is
exposed so that the inverse regrading has `K_k = C^(n-k)` definitionally. -/
@[expose, simps]
def embeddingDownIntUpIntSub (n : ℤ) : (down ℤ).Embedding (up ℤ) where
  f k := n - k
  injective_f _ _ h := by simpa using h
  rel {i j} h := by simp only [up_Rel, down_Rel] at h ⊢; omega

instance (n : ℤ) : (embeddingDownIntUpIntSub n).IsTruncGE where
  rel' {i j} h := by simp only [up_Rel, down_Rel, embeddingDownIntUpIntSub_f] at h ⊢; omega
  mem_next {_ k'} _ := ⟨n - k', by simp⟩

instance (n : ℤ) : (embeddingDownIntUpIntSub n).IsTruncLE where
  mem_prev {i' _} _ := ⟨n - i', by simp⟩

end ComplexShape

namespace ChainComplex

open HomologicalComplex ComplexShape

section HasZeroMorphisms

variable (C : Type*) [Category* C] [HasZeroMorphisms C] (n : ℤ)

/-- The equivalence of categories `ChainComplex C ℤ ≌ CochainComplex C ℤ` regrading a chain
complex `K` into the cochain complex with `C^k = K_(n-k)` and the same differential. Its body is
exposed so that statements about its functor, inverse, unit and counit, such as
`regradeEquivalence_unitIso_hom_app_f` and `regradeIsoShift`, type-check with `C^k = K_(n-k)`
definitionally. -/
@[expose]
noncomputable def regradeEquivalence : ChainComplex C ℤ ≌ CochainComplex C ℤ where
  functor := (embeddingUpIntDownIntSub n).restrictionFunctor C
  inverse := (embeddingDownIntUpIntSub n).restrictionFunctor C
  unitIso := NatIso.ofComponents (fun K ↦ Hom.isoOfComponents (fun k ↦ K.XIsoOfEq (by simp))
    (fun _ _ _ ↦ (K.XIsoOfEq_hom_comp_d _ _).trans (K.d_comp_XIsoOfEq_hom _ _).symm))
    (fun φ ↦ by ext k; exact XIsoOfEq_hom_naturality φ (by simp))
  counitIso := NatIso.ofComponents (fun K ↦ Hom.isoOfComponents (fun k ↦ K.XIsoOfEq (by simp))
    (fun _ _ _ ↦ (K.XIsoOfEq_hom_comp_d _ _).trans (K.d_comp_XIsoOfEq_hom _ _).symm))
    (fun φ ↦ by ext k; exact XIsoOfEq_hom_naturality φ (by simp))
  functor_unitIso_comp K := by
    ext k
    dsimp [Hom.isoOfComponents]
    exact (K.XIsoOfEq_hom_comp_XIsoOfEq_hom (by simp) (by simp)).trans rfl

/-- The regrading functor is the restriction along `k ↦ n - k`. -/
@[simp] theorem regradeEquivalence_functor :
    (regradeEquivalence C n).functor = (embeddingUpIntDownIntSub n).restrictionFunctor C :=
  (rfl)

/-- The inverse of the regrading functor is the restriction along `k ↦ n - k`. -/
@[simp] theorem regradeEquivalence_inverse :
    (regradeEquivalence C n).inverse = (embeddingDownIntUpIntSub n).restrictionFunctor C :=
  (rfl)

/-- In degree `k`, the unit of `regradeEquivalence` is the identification `K_k = K_(n-(n-k))`. -/
@[simp] theorem regradeEquivalence_unitIso_hom_app_f (K : ChainComplex C ℤ) (k : ℤ) :
    ((regradeEquivalence C n).unitIso.hom.app K).f k =
      (K.XIsoOfEq (show k = n - (n - k) by omega)).hom :=
  (rfl)

/-- In degree `k`, the inverse of the unit of `regradeEquivalence` is the identification
`K_(n-(n-k)) = K_k`. -/
@[simp] theorem regradeEquivalence_unitIso_inv_app_f (K : ChainComplex C ℤ) (k : ℤ) :
    ((regradeEquivalence C n).unitIso.inv.app K).f k =
      (K.XIsoOfEq (show k = n - (n - k) by omega)).inv :=
  (rfl)

/-- In degree `k`, the counit of `regradeEquivalence` is the identification `K^(n-(n-k)) = K^k`. -/
@[simp] theorem regradeEquivalence_counitIso_hom_app_f (K : CochainComplex C ℤ) (k : ℤ) :
    ((regradeEquivalence C n).counitIso.hom.app K).f k =
      (K.XIsoOfEq (show n - (n - k) = k by omega)).hom :=
  (rfl)

/-- In degree `k`, the inverse of the counit of `regradeEquivalence` is the identification
`K^k = K^(n-(n-k))`. -/
@[simp] theorem regradeEquivalence_counitIso_inv_app_f (K : CochainComplex C ℤ) (k : ℤ) :
    ((regradeEquivalence C n).counitIso.inv.app K).f k =
      (K.XIsoOfEq (show n - (n - k) = k by omega)).inv :=
  (rfl)

variable {C}

/-- For `n = n'`, the regradings of `K` by `n` and by `n'` are isomorphic, through the
identifications `K_(n-k) = K_(n'-k)`. The two regradings are not definitionally equal when `n` and
`n'` are only propositionally equal, as for `(n₁ + n₂) + n₃` and `n₁ + (n₂ + n₃)`. -/
noncomputable def regradeIsoOfEq {n n' : ℤ} (h : n = n') (K : ChainComplex C ℤ) :
    K.restriction (embeddingUpIntDownIntSub n) ≅ K.restriction (embeddingUpIntDownIntSub n') :=
  Hom.isoOfComponents (fun k ↦ K.XIsoOfEq (show n - k = n' - k by rw [h]))
    (fun _ _ _ ↦ (K.XIsoOfEq_hom_comp_d _ _).trans (K.d_comp_XIsoOfEq_hom _ _).symm)

/-- In degree `k`, `regradeIsoOfEq` is the identification `K_(n-k) = K_(n'-k)`. -/
@[simp] theorem regradeIsoOfEq_hom_f {n n' : ℤ} (h : n = n') (K : ChainComplex C ℤ) (k : ℤ) :
    (regradeIsoOfEq h K).hom.f k = (K.XIsoOfEq (show n - k = n' - k by rw [h])).hom :=
  (rfl)

/-- In degree `k`, the inverse of `regradeIsoOfEq` is the identification `K_(n'-k) = K_(n-k)`. -/
@[simp] theorem regradeIsoOfEq_inv_f {n n' : ℤ} (h : n = n') (K : ChainComplex C ℤ) (k : ℤ) :
    (regradeIsoOfEq h K).inv.f k = (K.XIsoOfEq (show n - k = n' - k by rw [h])).inv :=
  (rfl)

/-- Regrading along `n = n` is the identity. -/
@[simp] theorem regradeIsoOfEq_refl (K : ChainComplex C ℤ) :
    regradeIsoOfEq (rfl : n = n) K = Iso.refl _ := by
  ext k
  simp only [regradeIsoOfEq_hom_f, XIsoOfEq_rfl, Iso.refl_hom, id_f]
  -- The regraded object `(K.restriction _).X k` is `K.X (n - k)` by definition of the restriction.
  rfl

/-- `regradeIsoOfEq` is natural in the chain complex. -/
@[reassoc]
theorem regradeIsoOfEq_hom_naturality {n n' : ℤ} (h : n = n') {K L : ChainComplex C ℤ}
    (φ : K ⟶ L) :
    restrictionMap φ (embeddingUpIntDownIntSub n) ≫ (regradeIsoOfEq h L).hom =
      (regradeIsoOfEq h K).hom ≫ restrictionMap φ (embeddingUpIntDownIntSub n') := by
  ext k
  exact XIsoOfEq_hom_naturality φ (show n - k = n' - k by rw [h])

instance (K : ChainComplex C ℤ) (k : ℤ) [K.HasHomology (n - k)] :
    (K.restriction (embeddingUpIntDownIntSub n)).HasHomology k :=
  restriction.hasHomology K _ (k - 1) k (k + 1) (by simp) (by simp)
    (i' := n - (k - 1)) (j' := n - k) (k' := n - (k + 1)) (by simp) (by simp)
    (by simp) (by simp; omega) (by simp; omega)

/-- The homology of the regraded complex in degree `k` is the homology of the chain complex in
degree `n - k`. -/
noncomputable def regradeHomologyIso (K : ChainComplex C ℤ) (k : ℤ) [K.HasHomology (n - k)] :
    (K.restriction (embeddingUpIntDownIntSub n)).homology k ≅ K.homology (n - k) :=
  K.restrictionHomologyIso _ (k - 1) k (k + 1) (by simp) (by simp)
    (i' := n - (k - 1)) (j' := n - k) (k' := n - (k + 1)) (by simp) (by simp)
    (by simp) (by simp; omega) (by simp; omega)

/-- Under `regradeHomologyIso`, the homology class of a cycle of the regraded complex is the
homology class of the corresponding cycle of `K`. -/
@[reassoc (attr := simp)]
theorem homologyπ_regradeHomologyIso_hom (K : ChainComplex C ℤ) (k : ℤ)
    [K.HasHomology (n - k)] :
    (K.restriction (embeddingUpIntDownIntSub n)).homologyπ k ≫ (regradeHomologyIso n K k).hom =
      (K.restrictionCyclesIso _ k (k + 1) (by simp) (by simp) (by simp)
        (k' := n - (k + 1)) (by simp; omega)).hom ≫ K.homologyπ (n - k) :=
  K.homologyπ_restrictionHomologyIso_hom _ _ _ _ _ _ _ _ _ _ _

/-- The inverse of `regradeHomologyIso` sends the homology class of a cycle of `K` to the homology
class of the corresponding cycle of the regraded complex. -/
@[reassoc (attr := simp)]
theorem homologyπ_regradeHomologyIso_inv (K : ChainComplex C ℤ) (k : ℤ)
    [K.HasHomology (n - k)] :
    K.homologyπ (n - k) ≫ (regradeHomologyIso n K k).inv =
      (K.restrictionCyclesIso _ k (k + 1) (by simp) (by simp) (by simp)
        (k' := n - (k + 1)) (by simp; omega)).inv ≫
        (K.restriction (embeddingUpIntDownIntSub n)).homologyπ k :=
  K.homologyπ_restrictionHomologyIso_inv _ _ _ _ _ _ _ _ _ _ _

/-- The comparison `regradeHomologyIso` is compatible with the inclusions of homology into
opcycles. -/
@[reassoc (attr := simp)]
theorem regradeHomologyIso_hom_homologyι (K : ChainComplex C ℤ) (k : ℤ)
    [K.HasHomology (n - k)] :
    (regradeHomologyIso n K k).hom ≫ K.homologyι (n - k) =
      (K.restriction (embeddingUpIntDownIntSub n)).homologyι k ≫
        (K.restrictionOpcyclesIso _ (k - 1) k (by simp) (i' := n - (k - 1)) (by simp) (by simp)
          (by simp; omega)).hom :=
  K.restrictionHomologyIso_hom_homologyι _ _ _ _ _ _ _ _ _ _ _

/-- The inverse of `regradeHomologyIso` is compatible with the inclusions of homology into
opcycles. -/
@[reassoc (attr := simp)]
theorem regradeHomologyIso_inv_homologyι (K : ChainComplex C ℤ) (k : ℤ)
    [K.HasHomology (n - k)] :
    (regradeHomologyIso n K k).inv ≫ (K.restriction (embeddingUpIntDownIntSub n)).homologyι k =
      K.homologyι (n - k) ≫
        (K.restrictionOpcyclesIso _ (k - 1) k (by simp) (i' := n - (k - 1)) (by simp) (by simp)
          (by simp; omega)).inv :=
  K.restrictionHomologyIso_inv_homologyι _ _ _ _ _ _ _ _ _ _ _

/-- The identification of the homology of the regraded complex is natural. -/
@[reassoc]
theorem regradeHomologyIso_hom_naturality {K L : ChainComplex C ℤ} (φ : K ⟶ L) (k : ℤ)
    [K.HasHomology (n - k)] [L.HasHomology (n - k)] :
    homologyMap (restrictionMap φ (embeddingUpIntDownIntSub n)) k ≫
        (regradeHomologyIso n L k).hom =
      (regradeHomologyIso n K k).hom ≫ homologyMap φ (n - k) := by
  rw [← cancel_mono (L.homologyι (n - k))]
  simp only [Category.assoc, regradeHomologyIso_hom_homologyι, homologyι_naturality,
    homologyι_naturality_assoc, regradeHomologyIso_hom_homologyι_assoc]
  congr 1
  rw [← cancel_epi ((K.restriction (embeddingUpIntDownIntSub n)).pOpcycles k),
    p_opcyclesMap_assoc,
    restrictionMap_f' φ _ (by simp : (embeddingUpIntDownIntSub n).f k = n - k)]
  simp

end HasZeroMorphisms

section Preadditive

variable (C : Type*) [Category* C] [Preadditive C] (n : ℤ)

/-- The regrading by `n` agrees with Mathlib's `cochainComplexEquivalence` followed by the shift
by `-n`, up to the sign `(-1)^(n k)` in degree `k`: the shift multiplies the differential by
`(-1)^n`, while the regrading keeps it. -/
noncomputable def regradeIsoShift :
    (regradeEquivalence C n).functor ≅
      (cochainComplexEquivalence C).functor ⋙ CategoryTheory.shiftFunctor _ (-n) :=
  NatIso.ofComponents
    (fun K ↦ Hom.isoOfComponents (fun k ↦ (k * n).negOnePow • K.XIsoOfEq (by simp; omega))
      (fun k l hkl ↦ by
        obtain rfl : l = k + 1 := by simpa using hkl.symm
        -- Both differentials unfold to differentials of `K`: the regraded one by definition of
        -- `restriction`, the shifted one as `(-1)^(-n) • K.d` by definition of the shift.
        have hd : ((k * n).negOnePow • K.XIsoOfEq (show n - k = -(k + -n) by omega)).hom ≫
            ((-n).negOnePow • K.d (-(k + -n)) (-(k + 1 + -n))) =
            K.d (n - k) (n - (k + 1)) ≫ (((k + 1) * n).negOnePow •
              K.XIsoOfEq (show n - (k + 1) = -(k + 1 + -n) by omega)).hom := by
          simp only [Preadditive.smul_iso_hom, Units.smul_def, Preadditive.zsmul_comp,
            Preadditive.comp_zsmul, smul_smul, XIsoOfEq_hom_comp_d, d_comp_XIsoOfEq_hom,
            Int.negOnePow_neg, ← Units.val_mul, ← Int.negOnePow_add]
          congr 3
          ring
        exact hd))
    (fun {K L} φ ↦ by
      ext k
      -- The components of the regraded and shifted morphisms are components of `φ`.
      have hφ : φ.f (n - k) ≫ ((k * n).negOnePow •
            L.XIsoOfEq (show n - k = -(k + -n) by omega)).hom =
          ((k * n).negOnePow • K.XIsoOfEq (show n - k = -(k + -n) by omega)).hom ≫
            φ.f (-(k + -n)) := by
        simp only [Preadditive.smul_iso_hom, Units.smul_def, Preadditive.zsmul_comp,
          Preadditive.comp_zsmul, XIsoOfEq_hom_naturality]
      exact hφ)

/-- In degree `k`, the comparison `regradeIsoShift` is the identification `K_(n-k) = K_(n-k)`
twisted by the sign `(-1)^(k n)`. -/
@[simp]
theorem regradeIsoShift_hom_app_f (K : ChainComplex C ℤ) (k : ℤ) :
    ((regradeIsoShift C n).hom.app K).f k =
      (k * n).negOnePow • (K.XIsoOfEq (show n - k = -(k + -n) by omega)).hom :=
  (rfl)

/-- In degree `k`, the inverse of `regradeIsoShift` is the identification `K_(n-k) = K_(n-k)`
twisted by the sign `(-1)^(k n)`. -/
@[simp]
theorem regradeIsoShift_inv_app_f (K : ChainComplex C ℤ) (k : ℤ) :
    ((regradeIsoShift C n).inv.app K).f k =
      (k * n).negOnePow • (K.XIsoOfEq (show n - k = -(k + -n) by omega)).inv := by
  rw [← Int.units_inv_eq_self (k * n).negOnePow]
  rfl

end Preadditive

end ChainComplex

namespace CochainComplex

open HomologicalComplex ComplexShape

/-! ### Restriction of a cochain complex along `n ↦ -n`

The inverse of Mathlib's `ChainComplex.cochainComplexEquivalence` reads a cochain complex `K` as
the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ`, the restriction of `K` along
`ComplexShape.embeddingDownIntUpInt`. Its cycles and homology in degree `i` are those of `K` in
degree `-i`. -/

variable {C : Type*} [Category* C] [HasZeroMorphisms C] (K : CochainComplex C ℤ)

section Homology

variable (i j : ℤ) (h : i + j = 0)
  [K.HasHomology j] [(K.restriction embeddingDownIntUpInt).HasHomology i]

/-- The cycles of the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ` in degree `i` are those of the cochain
complex `K` in degree `j = -i`. -/
noncomputable def restrictionDownIntUpIntCyclesIso :
    (K.restriction embeddingDownIntUpInt).cycles i ≅ K.cycles j :=
  K.restrictionCyclesIso embeddingDownIntUpInt i (i - 1) ((down ℤ).next_eq' (by simp))
    (j' := j) (k' := j + 1) (by simp; omega) (by simp; omega) ((up ℤ).next_eq' (by simp))

/-- `CochainComplex.restrictionDownIntUpIntCyclesIso` is compatible with the inclusions of the
cycles. -/
@[reassoc (attr := simp)]
lemma restrictionDownIntUpIntCyclesIso_hom_iCycles :
    (K.restrictionDownIntUpIntCyclesIso i j h).hom ≫ K.iCycles j =
      (K.restriction embeddingDownIntUpInt).iCycles i ≫
        (K.restrictionXIso embeddingDownIntUpInt
          (show embeddingDownIntUpInt.f i = j by simp; omega)).hom :=
  K.restrictionCyclesIso_hom_iCycles ..

/-- The inverse of `CochainComplex.restrictionDownIntUpIntCyclesIso` is compatible with the
inclusions of the cycles. -/
@[reassoc (attr := simp)]
lemma restrictionDownIntUpIntCyclesIso_inv_iCycles :
    (K.restrictionDownIntUpIntCyclesIso i j h).inv ≫
        (K.restriction embeddingDownIntUpInt).iCycles i =
      K.iCycles j ≫ (K.restrictionXIso embeddingDownIntUpInt
          (show embeddingDownIntUpInt.f i = j by simp; omega)).inv :=
  K.restrictionCyclesIso_inv_iCycles ..

/-- The homology of the chain complex `K⁻` with `K⁻ᵢ = K⁻ⁱ` in degree `i` is that of the cochain
complex `K` in degree `j = -i`. -/
noncomputable def restrictionDownIntUpIntHomologyIso :
    (K.restriction embeddingDownIntUpInt).homology i ≅ K.homology j :=
  K.restrictionHomologyIso embeddingDownIntUpInt (i + 1) i (i - 1)
    ((down ℤ).prev_eq' (by simp)) ((down ℤ).next_eq' (by simp))
    (i' := j - 1) (k' := j + 1) (by simp; omega) (by simp; omega) (by simp; omega)
    ((up ℤ).prev_eq' (by simp)) ((up ℤ).next_eq' (by simp))

/-- Under `CochainComplex.restrictionDownIntUpIntHomologyIso`, the homology class of a cycle of
`K⁻` is the homology class of the corresponding cycle of `K`. -/
@[reassoc (attr := simp)]
lemma homologyπ_restrictionDownIntUpIntHomologyIso_hom :
    (K.restriction embeddingDownIntUpInt).homologyπ i ≫
        (K.restrictionDownIntUpIntHomologyIso i j h).hom =
      (K.restrictionDownIntUpIntCyclesIso i j h).hom ≫ K.homologyπ j :=
  K.homologyπ_restrictionHomologyIso_hom ..

/-- The inverse of `CochainComplex.restrictionDownIntUpIntHomologyIso` sends the homology class of
a cycle of `K` to the homology class of the corresponding cycle of `K⁻`. -/
@[reassoc (attr := simp)]
lemma homologyπ_restrictionDownIntUpIntHomologyIso_inv :
    K.homologyπ j ≫ (K.restrictionDownIntUpIntHomologyIso i j h).inv =
      (K.restrictionDownIntUpIntCyclesIso i j h).inv ≫
        (K.restriction embeddingDownIntUpInt).homologyπ i :=
  K.homologyπ_restrictionHomologyIso_inv ..

include h in
/-- If the cycles of `K` split off in degree `j = -i`, then those of `K⁻` split off in degree
`i`. -/
lemma isSplitMono_restrictionDownIntUpInt_iCycles [IsSplitMono (K.iCycles j)] :
    IsSplitMono ((K.restriction embeddingDownIntUpInt).iCycles i) :=
  IsSplitMono.mk'
    { retraction := (K.restrictionXIso embeddingDownIntUpInt
        (show embeddingDownIntUpInt.f i = j by simp; omega)).hom ≫
          retraction (K.iCycles j) ≫ (K.restrictionDownIntUpIntCyclesIso i j h).inv
      id := by
        rw [← restrictionDownIntUpIntCyclesIso_hom_iCycles_assoc K i j h, IsSplitMono.id_assoc,
          Iso.hom_inv_id] }

include h in
/-- If the cycles of `K` are projective in degree `j = -i`, then so are those of `K⁻` in degree
`i`. -/
lemma projective_restrictionDownIntUpInt_cycles [Projective (K.cycles j)] :
    Projective ((K.restriction embeddingDownIntUpInt).cycles i) :=
  Projective.of_iso (K.restrictionDownIntUpIntCyclesIso i j h).symm inferInstance

end Homology

end CochainComplex

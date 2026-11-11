/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Complex
public import Mathlib.LinearAlgebra.StdBasis

/-!
# Enhanced-state coordinates for the Khovanov complex

Each quantum component of the normalized tensor complex has a finite basis of enhanced states.
We index a state by its subset of B-smoothings and label its actual resolved circles by `1` and
`X`. The two degree constraints are built into the index, so this also covers absent bidegrees
and the empty diagram without exceptional choices of basis.

`khovanovEnhancedBasis` gives this basis, and `khovanovEnhancedComplex` is the native cochain
complex of finitely supported coefficient vectors in it. The comparison
`khovanovEnhancedComplexIso` is a cochain isomorphism, not just an equality of ranks. Its
coordinate formula reads the circle-basis coefficients of each state projection. Thus the
computational model retains the original signed saddle differential, and can be used to
transport maps and homology from the tensor model.

## References

* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
* D. Bar-Natan, *On Khovanov's categorification of the Jones polynomial*,
  Algebr. Geom. Topol. 2 (2002), §2.2.
-/

public section

noncomputable section

open CategoryTheory Limits Finset

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n)

/-- Enhanced states of normalized bidegree `(i,j)`, indexed by their B-smoothing subsets.
`false` labels a circle by `1`, and `true` labels it by `X`. -/
abbrev EnhancedStateAt (i j : ℤ) :=
  Σ S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount},
    {l : D.toPDCode.ResolvedCircle (PDCode.cubeState S.1) → Bool //
      Khovanov.labelingQuantumDegree _ l = j - D.stateQuantumShift (PDCode.cubeState S.1)}

/-- Forgetting the degree constraints gives an enhanced state on the native circle sets. -/
def EnhancedStateAt.toEnhancedState {i j : ℤ} (e : D.EnhancedStateAt i j) :
    D.toPDCode.EnhancedState :=
  ⟨PDCode.cubeState e.1.1, e.2.1⟩

/-- Forgetting the constraints retains both the smoothing and its dependent circle labels. -/
theorem EnhancedStateAt.toEnhancedState_def {i j : ℤ} (e : D.EnhancedStateAt i j) :
    e.toEnhancedState D = ⟨PDCode.cubeState e.1.1, e.2.1⟩ := (rfl)

/-- Forgetting the constraints preserves the smoothing state. -/
@[simp]
theorem EnhancedStateAt.toEnhancedState_fst {i j : ℤ} (e : D.EnhancedStateAt i j) :
    (e.toEnhancedState D).1 = PDCode.cubeState e.1.1 := (rfl)

/-- Forgetting the constraints preserves the circle labels on the corresponding smoothing. -/
@[simp]
theorem EnhancedStateAt.toEnhancedState_snd {i j : ℤ} (e : D.EnhancedStateAt i j) :
    HEq (e.toEnhancedState D).2 e.2.1 := (HEq.rfl)

/-- The underlying enhanced state has the specified cochain degree. -/
-- Simplify before the state projection erases the enhanced-state degree constraint.
@[simp↓]
theorem EnhancedStateAt.stateCochainDegree_toEnhancedState {i j : ℤ} (e : D.EnhancedStateAt i j) :
    D.stateCochainDegree (e.toEnhancedState D).1 = i := by
  simp only [EnhancedStateAt.toEnhancedState_fst, stateCochainDegree_cubeState, e.1.2]
  omega

/-- The underlying enhanced state has the specified quantum degree. -/
@[simp]
theorem EnhancedStateAt.enhancedQuantumDegree_toEnhancedState {i j : ℤ}
    (e : D.EnhancedStateAt i j) :
    D.enhancedQuantumDegree (e.toEnhancedState D) = j := by
  simp only [EnhancedStateAt.toEnhancedState_def, enhancedQuantumDegree_def, e.2.2]
  omega

/-- Cube-subset indexing gives exactly the native enhanced states of bidegree `(i,j)`. -/
def enhancedStateAtEquiv (i j : ℤ) :
    D.EnhancedStateAt i j ≃
      {e : D.toPDCode.EnhancedState //
        D.stateCochainDegree e.1 = i ∧ D.enhancedQuantumDegree e = j} :=
  Equiv.ofBijective
    (fun e ↦ ⟨e.toEnhancedState D, e.stateCochainDegree_toEnhancedState D,
      e.enhancedQuantumDegree_toEnhancedState D⟩)
    ⟨by
      rintro ⟨S, l⟩ ⟨T, k⟩ h
      have hST : S = T := Subtype.ext
        (PDCode.cubeState_injective (congrArg (fun e ↦ e.1.1) h))
      subst T
      congr 1
      apply Subtype.ext
      exact eq_of_heq (Sigma.mk.inj_iff.mp (congrArg Subtype.val h)).2,
    by
      rintro ⟨⟨s, l⟩, hi, hj⟩
      obtain ⟨S, rfl⟩ := PDCode.cubeState_bijective.surjective s
      refine ⟨⟨⟨S, ?_⟩, ⟨l, ?_⟩⟩, rfl⟩
      · rw [stateCochainDegree_cubeState] at hi
        omega
      · rw [enhancedQuantumDegree_def] at hj
        dsimp only at hj ⊢
        omega⟩

/-- The enhanced-state equivalence forgets only the two degree constraints. -/
@[simp]
theorem enhancedStateAtEquiv_apply_val {i j : ℤ} (e : D.EnhancedStateAt i j) :
    (D.enhancedStateAtEquiv i j e).1 = e.toEnhancedState D := (rfl)

variable (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R] (j : ℤ)

/-- The enhanced-state basis of a normalized quantum-component term, formed from the
circle-piece bases of the state summands. -/
def khovanovEnhancedBasis (i : ℤ) :
    Module.Basis (D.EnhancedStateAt i j) R ((D.khovanovComplex hD R j).X i) :=
  (Pi.basis fun S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount} ↦
    Khovanov.circlePieceBasis R (D.toPDCode.ResolvedCircle (PDCode.cubeState S.1))
      (j - D.stateQuantumShift (PDCode.cubeState S.1))).map
    ((D.khovanovComplexXIso hD R j i).toLinearEquiv.trans
      (ModuleCat.biproductIsoPi _).toLinearEquiv).symm

/-- Enhanced-state coordinates are the circle-basis coordinates of the corresponding
state projection. This formula does not require unfolding the basis construction. -/
@[simp]
theorem khovanovEnhancedBasis_repr (i : ℤ) (x : (D.khovanovComplex hD R j).X i)
    (e : D.EnhancedStateAt i j) :
    (D.khovanovEnhancedBasis hD R j i).repr x e =
      (Khovanov.circleBasis R _).repr
        ((eqToHom (D.resolutionCube_obj_normalized hD R j e.1.1)).hom
          ((D.khovanovComplexπ hD R j e.1).hom x) : Khovanov.CircleTensor R _) e.2.1 := by
  simp only [khovanovEnhancedBasis, Module.Basis.map_repr, LinearEquiv.symm_symm,
    LinearEquiv.trans_apply, Pi.basis_repr, Khovanov.circlePieceBasis_repr_apply]
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    khovanovComplexXIso_biproductIsoPi_apply]

/-- A basis vector is the circle-piece basis vector included in its state summand. -/
@[simp]
theorem khovanovEnhancedBasis_apply (i : ℤ) (e : D.EnhancedStateAt i j) :
    D.khovanovEnhancedBasis hD R j i e =
      (D.khovanovComplexι hD R j e.1).hom
        ((eqToHom (D.resolutionCube_obj_normalized hD R j e.1.1).symm).hom
          (Khovanov.circlePieceBasis R
            (D.toPDCode.ResolvedCircle (PDCode.cubeState e.1.1))
            (j - D.stateQuantumShift (PDCode.cubeState e.1.1)) e.2)) := by
  classical
  apply ((D.khovanovComplexXIso hD R j i).toLinearEquiv.trans
    (ModuleCat.biproductIsoPi _).toLinearEquiv).injective
  simp only [khovanovEnhancedBasis, Module.Basis.map_apply, LinearEquiv.apply_symm_apply,
    Pi.basis_apply, LinearEquiv.trans_apply]
  apply funext
  intro T
  rw [Iso.toLinearEquiv_apply, Iso.toLinearEquiv_apply,
    khovanovComplexXIso_biproductIsoPi_apply]
  by_cases h : e.1 = T
  · subst T
    simp only [Pi.single_eq_same, ← ModuleCat.comp_apply,
      khovanovComplexι_π_self, ModuleCat.id_apply]
    exact (ModuleCat.hom_inv_apply
      (eqToIso (D.resolutionCube_obj_normalized hD R j e.1.1)) _).symm
  · rw [← LinearMap.comp_apply (D.khovanovComplexπ hD R j T).hom
      (D.khovanovComplexι hD R j e.1).hom, ← ModuleCat.hom_comp,
      khovanovComplexι_π_of_ne _ _ _ _ h]
    simp only [Pi.single_eq_of_ne (Ne.symm h), ModuleCat.hom_zero, LinearMap.zero_apply,
      map_zero]

/-- The finite-free coefficient model of the normalized quantum component. Its differential
is the signed saddle differential expressed in the enhanced-state bases.
The body is exposed so its term carriers elaborate as coefficient vectors in importing files. -/
@[expose] def khovanovEnhancedComplex : CochainComplex (ModuleCat.{u} R) ℤ where
  X i := ModuleCat.of R (D.EnhancedStateAt i j →₀ R)
  d i k := ModuleCat.ofHom
    ((D.khovanovEnhancedBasis hD R j k).repr.toLinearMap.comp
      (((D.khovanovComplex hD R j).d i k).hom.comp
        (D.khovanovEnhancedBasis hD R j i).repr.symm.toLinearMap))
  shape i k hik := by
    apply ModuleCat.hom_ext
    simp [(D.khovanovComplex hD R j).shape i k hik]
  d_comp_d' i k l _ _ := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply,
      LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    rw [← ModuleCat.comp_apply, (D.khovanovComplex hD R j).d_comp_d]
    simp

/-- Every coefficient-vector term is free, including absent bidegrees. -/
instance (i : ℤ) : Module.Free R ((D.khovanovEnhancedComplex hD R j).X i) :=
  inferInstanceAs (Module.Free R (D.EnhancedStateAt i j →₀ R))

/-- Every coefficient-vector term is finitely generated. -/
instance (i : ℤ) : Module.Finite R ((D.khovanovEnhancedComplex hD R j).X i) := by
  classical
  exact inferInstanceAs (Module.Finite R (D.EnhancedStateAt i j →₀ R))

/-- The coordinate differential is conjugate to the actual tensor-complex differential. -/
@[simp]
theorem khovanovEnhancedComplex_d_apply (i k : ℤ) (x : D.EnhancedStateAt i j →₀ R) :
    ((D.khovanovEnhancedComplex hD R j).d i k).hom x =
      (D.khovanovEnhancedBasis hD R j k).repr
        (((D.khovanovComplex hD R j).d i k).hom
          ((D.khovanovEnhancedBasis hD R j i).repr.symm x)) := (rfl)

/-- The tensor and enhanced-state coefficient models are isomorphic as cochain complexes. -/
def khovanovEnhancedComplexIso :
    D.khovanovComplex hD R j ≅ D.khovanovEnhancedComplex hD R j :=
  HomologicalComplex.Hom.isoOfComponents
    (fun i ↦ (D.khovanovEnhancedBasis hD R j i).repr.toModuleIso)
    (by
      intros
      dsimp only [khovanovEnhancedComplex]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      simp [LinearEquiv.toModuleIso, LinearMap.comp_apply])

/-- The forward comparison takes enhanced-state coordinates. -/
@[simp]
theorem khovanovEnhancedComplexIso_hom_f (i : ℤ) :
    (D.khovanovEnhancedComplexIso hD R j).hom.f i =
      ModuleCat.ofHom (D.khovanovEnhancedBasis hD R j i).repr.toLinearMap := (rfl)

/-- The inverse comparison reconstructs an element from its enhanced-state coefficients. -/
@[simp]
theorem khovanovEnhancedComplexIso_inv_f (i : ℤ) :
    (D.khovanovEnhancedComplexIso hD R j).inv.f i =
      ModuleCat.ofHom (D.khovanovEnhancedBasis hD R j i).repr.symm.toLinearMap := (rfl)

/-- In enhanced-state coordinates the differential on a homogeneous state vector is the
sum over the missing crossings, with the original cube signs. Each cube edge in this formula
is the actual merge or split by `resolutionCube_map_homOfLE_insert_comp_resolutionCubeι`. -/
theorem khovanovEnhancedComplex_d_repr_ι {i : ℤ}
    (S : {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount})
    (x : (D.toPDCode.resolutionCube hD R
      (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).obj S.1) :
    ((D.khovanovEnhancedComplex hD R j).d i (i + 1)).hom
        ((D.khovanovEnhancedBasis hD R j i).repr
          ((D.khovanovComplexι hD R j S).hom x)) =
      ∑ a : (S.1ᶜ : Finset (Fin n)), ((-1 : ℤ) ^ #{b ∈ S.1 | b < a.1}) •
        (D.khovanovEnhancedBasis hD R j (i + 1)).repr
          ((D.khovanovComplexι hD R j ⟨insert a.1 S.1, by
            rw [card_insert_of_notMem (mem_compl.1 a.2), Nat.cast_succ, S.2]
            omega⟩).hom
              (((D.toPDCode.resolutionCube hD R
                (j - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).map
                  (homOfLE (S.1.subset_insert a.1))).hom x)) := by
  rw [khovanovEnhancedComplex_d_apply, LinearEquiv.symm_apply_apply,
    ← LinearMap.comp_apply, ← ModuleCat.hom_comp, ι_khovanovComplex_d]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, ModuleCat.hom_comp,
    LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply, map_sum, map_zsmul]
  -- The complex term inherits its sum and scalar action from the exposed Finsupp carrier.
  rfl

end TauCeti.OrientedPDCode

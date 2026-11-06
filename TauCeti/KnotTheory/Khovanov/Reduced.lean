/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.KnotTheory.Khovanov.Mark
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import TauCeti.Algebra.Homology.ShortComplex.ShortExact

/-!
# Marked-component reduction

The reduced complex is the image of the marked `X` action, with its quantum degree raised by
one. Thus its quantum component `j` is the image of `X : C_{j+1} → C_{j-1}`. Since the selected
circle contributes the free rank-two module with basis `1, X`, the image of `X` equals its
kernel over every commutative coefficient ring. The quotient by that image identifies with
the same reduced complex with the opposite quantum shift.

## References

* M. Khovanov, *Patterns in knot cohomology I*, Experiment. Math. 12 (2003), §3.
* M. Khovanov, *A categorification of the Jones polynomial*, Duke Math. J. 101 (2000), §§2–3.
-/

public section

noncomputable section

open CategoryTheory Limits Finset

namespace TauCeti.PDCode

universe u

variable {n : ℕ} (D : PDCode n) (p : D.Mark) (hD : D.IsPlanar)
  (R : Type u) [CommRing R] {j j' j'' : ℤ}

private theorem exists_resolutionCubeMarkX_eq (hj : j' = j - 2) (hj' : j'' = j' - 2)
    (S : Finset (Fin n)) (x : (D.resolutionCube hD R j').obj S)
    (hx : (D.resolutionCubeMarkX p hD R hj').app S x = 0) :
    ∃ y : (D.resolutionCube hD R j).obj S,
      (D.resolutionCubeMarkX p hD R hj).app S y = x := by
  let z := (D.resolutionCubeι hD R j' S).hom x
  have hz : z ∈ (Khovanov.circleQuantumGrading R (D.ResolvedCircle (cubeState S))).piece
      (j' - #S) := by
    rw [← range_resolutionCubeι]
    exact LinearMap.mem_range_self _ x
  have hX : Khovanov.circleX R (p.resolvedCircle (cubeState S)) z = 0 := by
    have h := D.resolutionCubeMarkX_app_comp_resolutionCubeι p hD R
      (j := j') (j' := j'') hj' S
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
      hx, map_zero] using (congrArg (fun f ↦ f.hom x) h).symm
  obtain ⟨y, hy, hxy⟩ := Khovanov.exists_circleX_eq_of_mem_piece_of_circleX_eq_zero
    (p.resolvedCircle (cubeState S)) hz hX
  have hyr : y ∈ LinearMap.range (D.resolutionCubeι hD R j S).hom := by
    rw [range_resolutionCubeι]
    have heq : j - (#S : ℤ) = j' - (#S : ℤ) + 2 := by omega
    rw [heq]
    exact hy
  obtain ⟨y', rfl⟩ := hyr
  refine ⟨y', D.resolutionCubeι_injective hD R j' S ?_⟩
  have h := D.resolutionCubeMarkX_app_comp_resolutionCubeι p hD R hj S
  exact (congrArg (fun f ↦ f.hom y') h).trans hxy

end TauCeti.PDCode

namespace TauCeti.OrientedPDCode

universe u

variable {n : ℕ} (D : OrientedPDCode n) (p : D.toPDCode.Mark)
  (hD : D.toPDCode.IsPlanar) (R : Type u) [CommRing R]

private theorem exists_khovanovComplexMarkX_eq {a b c : ℤ}
    (hab : b = a - 2) (hbc : c = b - 2) (i : ℤ)
    (x : (D.khovanovComplex hD R b).X i)
    (hx : (D.khovanovComplexMarkX p hD R hbc).f i x = 0) :
    ∃ y : (D.khovanovComplex hD R a).X i,
      (D.khovanovComplexMarkX p hD R hab).f i y = x := by
  classical
  let q := b - D.positiveCrossingCount + 2 * D.negativeCrossingCount
  let I := {S : Finset (Fin n) // (#S : ℤ) = i + D.negativeCrossingCount}
  have hs (S : I) : ∃ y : (D.toPDCode.resolutionCube hD R
      (a - D.positiveCrossingCount + 2 * D.negativeCrossingCount)).obj S.1,
      (D.toPDCode.resolutionCubeMarkX p hD R (j' := q) (by dsimp [q]; omega)).app S.1 y =
        (D.khovanovComplexπ hD R b S).hom x := by
    apply D.toPDCode.exists_resolutionCubeMarkX_eq p hD R
      (j'' := c - D.positiveCrossingCount + 2 * D.negativeCrossingCount)
      (by dsimp [q]; omega) (by dsimp [q]; omega)
    have hp := D.khovanovComplexMarkX_f_khovanovComplexπ p hD R hbc S
    simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, hx, map_zero] using
      (congrArg (fun f ↦ f.hom x) hp).symm
  choose y hy using hs
  refine ⟨∑ S : I, (D.khovanovComplexι hD R a S).hom (y S), ?_⟩
  have htotal := D.khovanovComplex_total hD R b i
  calc
    _ = ∑ S : I, (D.khovanovComplexι hD R b S).hom
        ((D.toPDCode.resolutionCubeMarkX p hD R (j' := q)
          (by dsimp [q]; omega)).app S.1 (y S)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro S _
      exact congrArg (fun f ↦ f.hom (y S))
        (D.khovanovComplexι_khovanovComplexMarkX_f p hD R hab S)
    _ = ∑ S : I, (D.khovanovComplexι hD R b S).hom
        ((D.khovanovComplexπ hD R b S).hom x) := by simp only [hy]
    _ = x := by
      simpa only [ModuleCat.hom_sum, LinearMap.sum_apply, ModuleCat.hom_comp,
        LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] using
        congrArg (fun f ↦ f.hom x) htotal

/-- At every quantum degree the marked `X` maps form an exact pair. Exactness is on the native
cochain complexes, rather than merely on their homology. -/
theorem khovanovComplexMarkX_exact {a b c : ℤ} (hab : b = a - 2) (hbc : c = b - 2) :
    (ShortComplex.mk (D.khovanovComplexMarkX p hD R hab)
      (D.khovanovComplexMarkX p hD R hbc)
      (D.khovanovComplexMarkX_comp_khovanovComplexMarkX p hD R hab hbc)).Exact := by
  apply HomologicalComplex.exact_of_degreewise_exact
  intro i
  rw [ShortComplex.moduleCat_exact_iff]
  exact D.exists_khovanovComplexMarkX_eq p hD R hab hbc i

/-- The reduced Khovanov complex at a mark, with the quantum normalization
`C_red_j = image(X : C_{j+1} → C_{j-1})`. In particular the reduced unknot lies in quantum degree
zero. The image is taken in the native abelian category of cochain complexes. -/
def reducedKhovanovComplex : GradedObject ℤ (CochainComplex (ModuleCat.{u} R) ℤ) :=
  fun j ↦ image (D.khovanovComplexMarkX p hD R (j := j + 1) (j' := j - 1) (by omega))

/-- The reduced quantum component is the image of the indicated marked action. -/
theorem reducedKhovanovComplex_apply (j : ℤ) :
    D.reducedKhovanovComplex p hD R j =
      image (D.khovanovComplexMarkX p hD R (j := j + 1) (j' := j - 1) (by omega)) := (rfl)

private def khovanovComplexMarkXArrowIso {a b c d : ℤ}
    (hab : b = a - 2) (hcd : d = c - 2) (hac : a = c) (hbd : b = d) :
    Arrow.mk (D.khovanovComplexMarkX p hD R hab) ≅
      Arrow.mk (D.khovanovComplexMarkX p hD R hcd) :=
  Arrow.isoMk (eqToIso (congrArg (D.khovanovComplex hD R) hac))
    (eqToIso (congrArg (D.khovanovComplex hD R) hbd)) (by
      subst c d
      simp)

private def reducedKhovanovComplexAddOneIso (j : ℤ) :
    D.reducedKhovanovComplex p hD R (j + 1) ≅
      image (D.khovanovComplexMarkX p hD R (j := j + 2) (j' := j) (by omega)) :=
  eqToIso (D.reducedKhovanovComplex_apply p hD R (j + 1)) ≪≫
    Limits.im.mapIso (D.khovanovComplexMarkXArrowIso p hD R
      (a := j + 1 + 1) (b := j + 1 - 1) (c := j + 2) (d := j)
      (by omega) (by omega) (by omega) (by omega))

private def reducedKhovanovComplexSubOneIso (j : ℤ) :
    D.reducedKhovanovComplex p hD R (j - 1) ≅
      image (D.khovanovComplexMarkX p hD R (j := j) (j' := j - 2) rfl) :=
  eqToIso (D.reducedKhovanovComplex_apply p hD R (j - 1)) ≪≫
    Limits.im.mapIso (D.khovanovComplexMarkXArrowIso p hD R
      (a := j - 1 + 1) (b := j - 1 - 1) (c := j) (d := j - 2)
      (by omega) rfl (by omega) (by omega))

/-- Inclusion of the quantum-shifted reduced complex in the unreduced complex:
`C_red⟨−1⟩_j → C_j`. -/
def reducedKhovanovComplexι (j : ℤ) :
    D.reducedKhovanovComplex p hD R (j + 1) ⟶ D.khovanovComplex hD R j :=
  (D.reducedKhovanovComplexAddOneIso p hD R j).hom ≫
    image.ι (D.khovanovComplexMarkX p hD R (j := j + 2) (j' := j) (by omega))

/-- Projection from the unreduced complex onto the oppositely shifted reduced complex:
`C_j → C_red⟨1⟩_j`. -/
def reducedKhovanovComplexπ (j : ℤ) :
    D.khovanovComplex hD R j ⟶ D.reducedKhovanovComplex p hD R (j - 1) :=
  factorThruImage (D.khovanovComplexMarkX p hD R (j := j) (j' := j - 2) rfl) ≫
    (D.reducedKhovanovComplexSubOneIso p hD R j).inv

/-- The reduced inclusion is the native image inclusion, followed by the quantum index
identification. -/
theorem reducedKhovanovComplexι_def (j : ℤ) :
    D.reducedKhovanovComplexι p hD R j =
      eqToHom (D.reducedKhovanovComplex_apply p hD R (j + 1)) ≫
        image.ι (D.khovanovComplexMarkX p hD R
          (j := j + 1 + 1) (j' := j + 1 - 1) (by omega)) ≫
          eqToHom (congrArg (D.khovanovComplex hD R) (show j + 1 - 1 = j by omega)) := by
  dsimp only [reducedKhovanovComplexι, reducedKhovanovComplexAddOneIso]
  dsimp only [Iso.trans, Functor.mapIso, eqToIso]
  simp only [Category.assoc, Limits.im_map]
  erw [image.map_ι]
  rfl

/-- The reduced projection is the native factorization through the marked image, preceded by
the quantum index identification. -/
theorem reducedKhovanovComplexπ_def (j : ℤ) :
    D.reducedKhovanovComplexπ p hD R j =
      eqToHom (congrArg (D.khovanovComplex hD R) (show j = j - 1 + 1 by omega)) ≫
        factorThruImage (D.khovanovComplexMarkX p hD R
          (j := j - 1 + 1) (j' := j - 1 - 1) (by omega)) ≫
          eqToHom (D.reducedKhovanovComplex_apply p hD R (j - 1)).symm := by
  dsimp only [reducedKhovanovComplexπ, reducedKhovanovComplexSubOneIso]
  dsimp only [Iso.trans, Functor.mapIso, eqToIso]
  simp only [← Category.assoc, Limits.im_map]
  erw [image.factor_map (D.khovanovComplexMarkXArrowIso p hD R
    (a := j - 1 + 1) (b := j - 1 - 1) (c := j) (d := j - 2)
    (by omega) rfl (by omega) (by omega)).inv]
  rfl

/-- The reduced inclusion is injective in the category of cochain complexes. -/
instance (j : ℤ) : Mono (D.reducedKhovanovComplexι p hD R j) := by
  unfold reducedKhovanovComplexι
  infer_instance

/-- The reduced projection is surjective in the category of cochain complexes. -/
instance (j : ℤ) : Epi (D.reducedKhovanovComplexπ p hD R j) := by
  unfold reducedKhovanovComplexπ
  infer_instance

/-- The reduced inclusion followed by the reduced projection vanishes. -/
@[reassoc (attr := simp)]
theorem reducedKhovanovComplexι_π (j : ℤ) :
    D.reducedKhovanovComplexι p hD R j ≫ D.reducedKhovanovComplexπ p hD R j = 0 := by
  simp only [reducedKhovanovComplexι, reducedKhovanovComplexπ, Category.assoc]
  rw [← Category.assoc (image.ι _) (factorThruImage _),
    comp_factorThruImage_eq_zero (image_ι_comp_eq_zero
      (D.khovanovComplexMarkX_comp_khovanovComplexMarkX p hD R (by omega) rfl))]
  simp

/-- The reduced/unreduced sequence in quantum degree `j`:
`0 → C_red_{j+1} → C_j → C_red_{j-1} → 0`. -/
def reducedKhovanovShortComplex (j : ℤ) :
    ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
  ShortComplex.mk (D.reducedKhovanovComplexι p hD R j)
    (D.reducedKhovanovComplexπ p hD R j) (D.reducedKhovanovComplexι_π p hD R j)

/-- The left object of the reduced/unreduced sequence is the shifted reduced complex. -/
@[simp]
theorem reducedKhovanovShortComplex_X₁ (j : ℤ) :
    (D.reducedKhovanovShortComplex p hD R j).X₁ =
      D.reducedKhovanovComplex p hD R (j + 1) := (rfl)

/-- The middle object of the reduced/unreduced sequence is the unreduced complex. -/
@[simp]
theorem reducedKhovanovShortComplex_X₂ (j : ℤ) :
    (D.reducedKhovanovShortComplex p hD R j).X₂ = D.khovanovComplex hD R j := (rfl)

/-- The right object of the reduced/unreduced sequence has the opposite quantum shift. -/
@[simp]
theorem reducedKhovanovShortComplex_X₃ (j : ℤ) :
    (D.reducedKhovanovShortComplex p hD R j).X₃ =
      D.reducedKhovanovComplex p hD R (j - 1) := (rfl)

/-- The reduced/unreduced sequence consists of the reduced inclusion and projection. This
constructor equation also identifies the dependent carriers of its two maps. -/
theorem reducedKhovanovShortComplex_def (j : ℤ) :
    D.reducedKhovanovShortComplex p hD R j =
      ShortComplex.mk (D.reducedKhovanovComplexι p hD R j)
        (D.reducedKhovanovComplexπ p hD R j)
        (D.reducedKhovanovComplexι_π p hD R j) := (rfl)

/-- The reduced/unreduced sequence is short exact over every commutative coefficient ring. -/
theorem reducedKhovanovShortComplex_shortExact (j : ℤ) :
    (D.reducedKhovanovShortComplex p hD R j).ShortExact := by
  let a := D.khovanovComplexMarkX p hD R (j := j + 2) (j' := j) (by omega)
  let b := D.khovanovComplexMarkX p hD R (j := j) (j' := j - 2) rfl
  have hab : a ≫ b = 0 :=
    D.khovanovComplexMarkX_comp_khovanovComplexMarkX p hD R (by omega) rfl
  let U := ShortComplex.mk (image.ι a) b (image_ι_comp_eq_zero hab)
  have hU : U.Exact := U.exact_of_f_is_kernel
    ((D.khovanovComplexMarkX_exact p hD R (by omega) rfl).isLimitImage')
  let V := ShortComplex.mk (image.ι a) (factorThruImage b)
    (comp_factorThruImage_eq_zero (image_ι_comp_eq_zero hab))
  have hV : V.ShortExact := hU.shortExact_factorThruImage
  let e : V ≅ D.reducedKhovanovShortComplex p hD R j :=
    ShortComplex.isoMk (D.reducedKhovanovComplexAddOneIso p hD R j).symm
      (Iso.refl _) (D.reducedKhovanovComplexSubOneIso p hD R j).symm
      (by simp [reducedKhovanovShortComplex, reducedKhovanovComplexι, V, a])
      (by simp [reducedKhovanovShortComplex, reducedKhovanovComplexπ, V, b])
  exact ShortComplex.shortExact_of_iso e hV

/-- The quotient model of the reduced complex, normalized so that quantum degree `j` is
`(C/XC)_{j+1}`. -/
def reducedKhovanovQuotientComplex : GradedObject ℤ (CochainComplex (ModuleCat.{u} R) ℤ) :=
  fun j ↦ cokernel (D.khovanovComplexMarkX p hD R
    (j := j + 3) (j' := j + 1) (by omega))

/-- The quotient model in quantum degree `j` is the cokernel of the marked action into
unreduced quantum degree `j + 1`. -/
theorem reducedKhovanovQuotientComplex_apply (j : ℤ) :
    D.reducedKhovanovQuotientComplex p hD R j =
      cokernel (D.khovanovComplexMarkX p hD R (j := j + 3) (j' := j + 1)
        (by omega)) := (rfl)

/-- The quotient map from unreduced quantum degree `j + 1` to the quotient model of reduced
quantum degree `j`. -/
def reducedKhovanovQuotientπ (j : ℤ) :
    D.khovanovComplex hD R (j + 1) ⟶ D.reducedKhovanovQuotientComplex p hD R j :=
  cokernel.π (D.khovanovComplexMarkX p hD R (j := j + 3) (j' := j + 1) (by omega)) ≫
    eqToHom (D.reducedKhovanovQuotientComplex_apply p hD R j).symm

/-- The quotient projection is the native cokernel projection followed by the identification
with the quotient model. -/
theorem reducedKhovanovQuotientπ_def (j : ℤ) :
    D.reducedKhovanovQuotientπ p hD R j =
      cokernel.π (D.khovanovComplexMarkX p hD R (j := j + 3) (j' := j + 1)
        (by omega)) ≫
          eqToHom (D.reducedKhovanovQuotientComplex_apply p hD R j).symm := (rfl)

/-- The incoming marked action vanishes after projection to the quotient model. -/
@[reassoc (attr := simp)]
theorem khovanovComplexMarkX_comp_reducedKhovanovQuotientπ (j : ℤ) :
    D.khovanovComplexMarkX p hD R (j := j + 3) (j' := j + 1) (by omega) ≫
      D.reducedKhovanovQuotientπ p hD R j = 0 := by
  simp [reducedKhovanovQuotientπ_def]

/-- The quotient projection exhibits the quotient model as the cokernel of the incoming
marked action, so maps annihilating that action descend uniquely to the quotient. -/
def reducedKhovanovQuotientπIsCokernel (j : ℤ) :
    IsColimit (CokernelCofork.ofπ (D.reducedKhovanovQuotientπ p hD R j)
      (D.khovanovComplexMarkX_comp_reducedKhovanovQuotientπ p hD R j)) :=
  IsCokernel.cokernelIso _ _ (cokernelIsCokernel _)
    (eqToIso (D.reducedKhovanovQuotientComplex_apply p hD R j).symm)
    (D.reducedKhovanovQuotientπ_def p hD R j).symm

/-- The canonical quotient map is surjective as a map of cochain complexes. -/
instance (j : ℤ) : Epi (D.reducedKhovanovQuotientπ p hD R j) := by
  unfold reducedKhovanovQuotientπ
  infer_instance

/-- The quotient model is canonically isomorphic to the image model of the reduced complex. -/
def reducedKhovanovQuotientIso (j : ℤ) :
    D.reducedKhovanovQuotientComplex p hD R j ≅ D.reducedKhovanovComplex p hD R j := by
  let a := D.khovanovComplexMarkX p hD R (j := j + 3) (j' := j + 1) (by omega)
  let b := D.khovanovComplexMarkX p hD R (j := j + 1) (j' := j - 1) (by omega)
  have hab : a ≫ b = 0 :=
    D.khovanovComplexMarkX_comp_khovanovComplexMarkX p hD R (by omega) (by omega)
  let T := ShortComplex.mk a b hab
  have hT : T.Exact := D.khovanovComplexMarkX_exact p hD R (by omega) (by omega)
  exact (cokernelIsCokernel a).coconePointUniqueUpToIso hT.isColimitImage ≪≫
    eqToIso (D.reducedKhovanovComplex_apply p hD R j).symm

/-- The quotient/image identification sends the quotient class of a cochain to its marked
`X` image. This characterizes the identification by the universal property of the quotient. -/
@[reassoc]
theorem reducedKhovanovQuotientπ_comp_reducedKhovanovQuotientIso_hom (j : ℤ) :
    D.reducedKhovanovQuotientπ p hD R j ≫
      (D.reducedKhovanovQuotientIso p hD R j).hom ≫
        eqToHom (D.reducedKhovanovComplex_apply p hD R j) =
      factorThruImage (D.khovanovComplexMarkX p hD R (j := j + 1) (j' := j - 1)
        (by omega)) := by
  dsimp only [reducedKhovanovQuotientπ, reducedKhovanovQuotientIso]
  dsimp only [Iso.trans, eqToIso]
  simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  erw [eqToHom_refl, Category.id_comp]
  exact IsColimit.comp_coconePointUniqueUpToIso_hom (cokernelIsCokernel _) _
    WalkingParallelPair.one

end TauCeti.OrientedPDCode

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ReidemeisterTorsion.Basic
public import Mathlib.RingTheory.Artinian.Module
public import TauCeti.Algebra.Homology.ModuleCat.OfMatrix
import Mathlib.Algebra.Group.Pi.Units

/-!
# Componentwise torsion over a finite product of fields

Let `C` be a `ℤ`-graded chain complex of modules over a commutative ring `A`, with an ordered
basis `c i : Basis (Fin (n i)) A (C.X i)` in each degree, and let `Q` be a reduced Artinian
`A`-algebra. Such a ring is canonically the finite product `∏ₘ Q ⧸ m` of its residue fields, one
for each maximal ideal `m` (`IsArtinianRing.equivPi`). The total quotient rings of the group ring
`ℤ[H]` of a finitely generated abelian group `H`, and of its Novikov completions, are of this kind.

For a ring homomorphism `φ : A →+* K`, the *scalar extension* of the based complex `(C, c)` along
`φ` is the complex `HomologicalComplex.extendScalarsOfBasis C c φ` of coordinate spaces
`Fin (n i) → K` whose differentials have as matrices the images under `φ` of the matrices of the
differentials of `C` in the bases `c i`, an instance of `ChainComplex.ofMatrix`. It is based by
the standard bases `ChainComplex.ofMatrixBasis`.

The *componentwise torsion* `HomologicalComplex.reidemeisterTorsionComponentwise C c Q` is the
element of `Q` whose component in each residue field `Q ⧸ m` is the torsion of the scalar extension
of `(C, c)` to `Q ⧸ m`. In particular it vanishes exactly on the components where that scalar
extension is not acyclic, which a single global zero convention would not record. Its image under
any homomorphism `ψ : Q →+* K` to a field is the torsion of the scalar extension of `(C, c)` along
`ψ ∘ algebraMap A Q` (`HomologicalComplex.map_reidemeisterTorsionComponentwise`): the kernel of `ψ`
is a maximal ideal of `Q`, and the torsion is compatible with the field homomorphism from the
corresponding residue field to `K`. Since `Q` embeds into the product of its residue fields, this
determines the componentwise torsion: any jointly injective family of homomorphisms from `Q` to
fields, such as the projections of a decomposition of `Q` as a product of fields, can be used to
compute it (`HomologicalComplex.eq_reidemeisterTorsionComponentwise_iff`).

When `A = F` is itself a field, the componentwise torsion is the image of the torsion
`HomologicalComplex.reidemeisterTorsion C c` of the based complex over `F`
(`HomologicalComplex.reidemeisterTorsionComponentwise_eq_algebraMap`), and for `Q = F` it is that
torsion.

## Main declarations

* `HomologicalComplex.extendScalarsOfBasis`: the scalar extension of a based complex along a ring
  homomorphism, on coordinate spaces.
* `HomologicalComplex.reidemeisterTorsion_extendScalarsOfBasis_comp`: the torsion of iterated
  scalar extensions to fields.
* `HomologicalComplex.reidemeisterTorsionComponentwise`: the componentwise torsion with values in a
  reduced Artinian algebra.
* `HomologicalComplex.map_reidemeisterTorsionComponentwise`: its image under a homomorphism to a
  field.
* `HomologicalComplex.eq_reidemeisterTorsionComponentwise_iff`: its characterization by a jointly
  injective family of homomorphisms to fields.
* `HomologicalComplex.map_reidemeisterTorsionComponentwise_eq_zero_iff`,
  `HomologicalComplex.isUnit_reidemeisterTorsionComponentwise_iff` and
  `HomologicalComplex.reidemeisterTorsionComponentwise_eq_zero_iff`: a component vanishes exactly
  when the corresponding scalar extension is not acyclic.

## References

* M. Hutchings, *Reidemeister torsion in generalized Morse theory*, Forum Math. 14 (2002),
  209–244, §2.
* V. Turaev, *Introduction to Combinatorial Torsions*, Birkhäuser 2001, Chapter I, §2.
-/

public section

noncomputable section

open CategoryTheory Module

universe u

namespace HomologicalComplex

variable {A : Type*} [CommRing A] (C : ChainComplex (ModuleCat A) ℤ) {n : ℤ → ℕ}
  (c : ∀ i, Basis (Fin (n i)) A (C.X i))

section ExtendScalars

variable {K : Type*} [CommRing K] (φ : A →+* K)

/-- The scalar extension of a based complex `(C, c)` over `A` along a ring homomorphism
`φ : A →+* K`: the complex of coordinate spaces `Fin (n i) → K` whose differential
`Kⁿ⁽ⁱ⁺¹⁾ → Kⁿ⁽ⁱ⁾` is given by the image under `φ` of the matrix of `d : Cᵢ₊₁ → Cᵢ` in the bases
`c (i + 1)` and `c i`. It is based by the standard bases `ChainComplex.ofMatrixBasis`. -/
abbrev extendScalarsOfBasis : ChainComplex (ModuleCat K) ℤ :=
  ChainComplex.ofMatrix (fun i ↦ (LinearMap.toMatrix (c (i + 1)) (c i) (C.d (i + 1) i).hom).map φ)
    fun i ↦ by
      rw [← Matrix.map_mul, ← LinearMap.toMatrix_comp, ← ModuleCat.hom_comp, C.d_comp_d,
        ModuleCat.hom_zero, map_zero, Matrix.map_zero _ φ.map_zero]

end ExtendScalars

section Field

variable {K L : Type*} [Field K] [Field L]

/-- The torsion of the scalar extension of a based complex to a field `K`, mapped by a
homomorphism of fields `σ : K →+* L`, is the torsion of the scalar extension to `L` along the
composite. -/
theorem reidemeisterTorsion_extendScalarsOfBasis_comp (φ : A →+* K) (σ : K →+* L) :
    (C.extendScalarsOfBasis c (σ.comp φ)).reidemeisterTorsion
        (ChainComplex.ofMatrixBasis _ _) =
      σ ((C.extendScalarsOfBasis c φ).reidemeisterTorsion (ChainComplex.ofMatrixBasis _ _)) := by
  refine (map_reidemeisterTorsion σ fun i ↦ ?_).symm
  rw [ChainComplex.toMatrix_ofMatrix_d, ChainComplex.toMatrix_ofMatrix_d, Matrix.map_map,
    RingHom.coe_comp]

/-- The torsion of the scalar extension of a based complex over a field `F` along a homomorphism
of fields `φ : F →+* K` is the image under `φ` of its torsion. -/
theorem reidemeisterTorsion_extendScalarsOfBasis {F : Type*} [Field F]
    (C : ChainComplex (ModuleCat F) ℤ) (c : ∀ i, Basis (Fin (n i)) F (C.X i)) (φ : F →+* K) :
    (C.extendScalarsOfBasis c φ).reidemeisterTorsion (ChainComplex.ofMatrixBasis _ _) =
      φ (C.reidemeisterTorsion c) :=
  (map_reidemeisterTorsion φ fun _ ↦ ChainComplex.toMatrix_ofMatrix_d ..).symm

end Field

section Componentwise

variable (Q : Type u) [CommRing Q] [Algebra A Q] [IsArtinianRing Q] [IsReduced Q]

/-- The componentwise torsion of a based complex `(C, c)` over `A`, with values in a reduced
Artinian `A`-algebra `Q`: the element of `Q` whose image in the residue field `Q ⧸ m` at each
maximal ideal `m` is the torsion of the scalar extension of `(C, c)` to `Q ⧸ m`. A component is
`0` exactly when that scalar extension is not acyclic or not bounded. -/
def reidemeisterTorsionComponentwise : Q :=
  (IsArtinianRing.equivPi Q).symm fun m ↦
    letI := Ideal.Quotient.field m.asIdeal
    reidemeisterTorsion (C.extendScalarsOfBasis c ((Ideal.Quotient.mk m.asIdeal).comp
      (algebraMap A Q))) (ChainComplex.ofMatrixBasis _ _)

variable {Q}

/-- **The components of the componentwise torsion.** The image of the componentwise torsion under a
homomorphism `ψ : Q →+* K` to a field is the torsion of the scalar extension of `(C, c)` along
`ψ ∘ algebraMap A Q`. -/
theorem map_reidemeisterTorsionComponentwise {K : Type*} [Field K] (ψ : Q →+* K) :
    ψ (C.reidemeisterTorsionComponentwise c Q) =
      (C.extendScalarsOfBasis c (ψ.comp (algebraMap A Q))).reidemeisterTorsion
        (ChainComplex.ofMatrixBasis _ _) := by
  -- The kernel of `ψ` is a prime, hence maximal, ideal `m`, and `ψ` factors through `Q ⧸ m`.
  have := RingHom.ker_isPrime ψ
  let m : MaximalSpectrum Q := ⟨RingHom.ker ψ, IsArtinianRing.isMaximal_of_isPrime _⟩
  let := @Ideal.Quotient.field _ _ m.asIdeal m.isMaximal
  let σ : Q ⧸ m.asIdeal →+* K := Ideal.Quotient.lift m.asIdeal ψ fun _ h ↦ h
  have hσ : σ.comp ((Ideal.Quotient.mk m.asIdeal).comp (algebraMap A Q)) =
      ψ.comp (algebraMap A Q) :=
    RingHom.ext fun _ ↦ Ideal.Quotient.lift_mk m.asIdeal ψ fun _ h ↦ h
  have hm : Ideal.Quotient.mk m.asIdeal (C.reidemeisterTorsionComponentwise c Q) =
      (C.extendScalarsOfBasis c ((Ideal.Quotient.mk m.asIdeal).comp
        (algebraMap A Q))).reidemeisterTorsion (ChainComplex.ofMatrixBasis _ _) := by
    rw [← IsArtinianRing.equivPi_apply, reidemeisterTorsionComponentwise,
      AlgEquiv.apply_symm_apply]
  rw [← hσ, reidemeisterTorsion_extendScalarsOfBasis_comp, ← hm]
  exact (Ideal.Quotient.lift_mk m.asIdeal ψ fun _ h ↦ h).symm

/-- The componentwise torsion is determined by its images under any jointly injective family of
homomorphisms `ψ j : Q →+* K j` to fields, such as the projections of a decomposition of `Q` as a
product of fields: an element of `Q` is the componentwise torsion if and only if its image under
each `ψ j` is the torsion of the scalar extension of `(C, c)` along `ψ j ∘ algebraMap A Q`. -/
theorem eq_reidemeisterTorsionComponentwise_iff {ι : Type*} {K : ι → Type*}
    [∀ j, Field (K j)] (ψ : ∀ j, Q →+* K j) (hψ : Function.Injective fun x j ↦ ψ j x) {x : Q} :
    x = C.reidemeisterTorsionComponentwise c Q ↔ ∀ j, ψ j x =
      (C.extendScalarsOfBasis c ((ψ j).comp (algebraMap A Q))).reidemeisterTorsion
        (ChainComplex.ofMatrixBasis _ _) := by
  simp_rw [← map_reidemeisterTorsionComponentwise]
  exact ⟨fun h j ↦ h ▸ rfl, fun h ↦ hψ (funext h)⟩

/-- The image of the componentwise torsion of a bounded complex under a homomorphism `ψ : Q →+* K`
to a field vanishes if and only if the scalar extension of `(C, c)` along `ψ ∘ algebraMap A Q` is
not acyclic. -/
theorem map_reidemeisterTorsionComponentwise_eq_zero_iff {K : Type*} [Field K] (ψ : Q →+* K)
    (hn : {i | n i ≠ 0}.Finite) :
    ψ (C.reidemeisterTorsionComponentwise c Q) = 0 ↔
      ¬(C.extendScalarsOfBasis c (ψ.comp (algebraMap A Q))).Acyclic := by
  rw [map_reidemeisterTorsionComponentwise, reidemeisterTorsion_eq_zero_iff _ _ hn]

/-- The componentwise torsion of a bounded complex is a unit if and only if its scalar extension
along every homomorphism from `Q` to a field is acyclic. It suffices to consider the residue fields
of `Q`, which lie in the same universe as `Q`. -/
theorem isUnit_reidemeisterTorsionComponentwise_iff (hn : {i | n i ≠ 0}.Finite) :
    IsUnit (C.reidemeisterTorsionComponentwise c Q) ↔ ∀ (K : Type u) [Field K] (ψ : Q →+* K),
      (C.extendScalarsOfBasis c (ψ.comp (algebraMap A Q))).Acyclic := by
  refine ⟨fun h K _ ψ ↦ ?_, fun h ↦ ?_⟩
  · rw [← not_not (a := Acyclic _), ← C.map_reidemeisterTorsionComponentwise_eq_zero_iff c ψ hn]
    exact (h.map ψ).ne_zero
  · rw [← MulEquiv.isUnit_map (IsArtinianRing.equivPi Q), Pi.isUnit_iff]
    intro m
    let := Ideal.Quotient.field m.asIdeal
    rw [isUnit_iff_ne_zero, IsArtinianRing.equivPi_apply, Ne,
      C.map_reidemeisterTorsionComponentwise_eq_zero_iff c (Ideal.Quotient.mk m.asIdeal) hn,
      not_not]
    exact h _ _

/-- The componentwise torsion of a bounded complex vanishes if and only if its scalar extension
along every homomorphism from `Q` to a field is not acyclic. It suffices to consider the residue
fields of `Q`, which lie in the same universe as `Q`. -/
theorem reidemeisterTorsionComponentwise_eq_zero_iff (hn : {i | n i ≠ 0}.Finite) :
    C.reidemeisterTorsionComponentwise c Q = 0 ↔ ∀ (K : Type u) [Field K] (ψ : Q →+* K),
      ¬(C.extendScalarsOfBasis c (ψ.comp (algebraMap A Q))).Acyclic := by
  refine ⟨fun h K _ ψ ↦ ?_, fun h ↦ (IsArtinianRing.equivPi Q).injective (funext fun m ↦ ?_)⟩
  · rw [← C.map_reidemeisterTorsionComponentwise_eq_zero_iff c ψ hn, h, map_zero]
  · let := Ideal.Quotient.field m.asIdeal
    rw [IsArtinianRing.equivPi_apply, map_zero, Pi.zero_apply,
      C.map_reidemeisterTorsionComponentwise_eq_zero_iff c (Ideal.Quotient.mk m.asIdeal) hn]
    exact h _ _

/-- Over a field `F`, the componentwise torsion with values in a reduced Artinian `F`-algebra `Q`
is the image in `Q` of the torsion of the based complex. -/
theorem reidemeisterTorsionComponentwise_eq_algebraMap {F : Type*} [Field F] [Algebra F Q]
    (C : ChainComplex (ModuleCat F) ℤ) (c : ∀ i, Basis (Fin (n i)) F (C.X i)) :
    C.reidemeisterTorsionComponentwise c Q = algebraMap F Q (C.reidemeisterTorsion c) := by
  let _ (m : MaximalSpectrum Q) : Field (Q ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  have hinj : Function.Injective fun (x : Q) (m : MaximalSpectrum Q) ↦
      Ideal.Quotient.mk m.asIdeal x := fun x y h ↦
    (IsArtinianRing.equivPi Q).injective (funext fun m ↦ by simpa using congrFun h m)
  refine ((C.eq_reidemeisterTorsionComponentwise_iff c _ hinj).2 fun m ↦ ?_).symm
  rw [reidemeisterTorsion_extendScalarsOfBasis, RingHom.comp_apply]

/-- Over a field `F`, the componentwise torsion with values in `F` itself is the torsion of the
based complex. -/
@[simp]
theorem reidemeisterTorsionComponentwise_self {F : Type u} [Field F]
    (C : ChainComplex (ModuleCat F) ℤ) (c : ∀ i, Basis (Fin (n i)) F (C.X i)) :
    C.reidemeisterTorsionComponentwise c F = C.reidemeisterTorsion c :=
  C.reidemeisterTorsionComponentwise_eq_algebraMap c

end Componentwise

end HomologicalComplex

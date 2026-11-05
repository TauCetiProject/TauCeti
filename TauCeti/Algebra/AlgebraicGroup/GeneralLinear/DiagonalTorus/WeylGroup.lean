/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.DiagonalizableGroup.Normalizer.FormalCharacter
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.GeneralLinear.DiagonalTorus.ClosedImmersion
public import TauCeti.Algebra.AlgebraicGroup.SplitTorus.Relabel
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Normalizer

/-!
# The scheme-theoretic Weyl group of the diagonal torus of `GL_N`

Let `T ⊆ GL_N` be the diagonal split torus over a commutative ring `R`, with character group
`X = ℤ^N` (written `Multiplicative (ULift (Fin N) →₀ ℤ)`). Its Weyl group
`BialgHom.weylGroup` consists of the automorphisms of `X` induced by inverse conjugation by
rational points normalizing the closed subgroup scheme `T`.

Conjugation by a permutation matrix permutes the diagonal entries of the generic point of `T`,
so it normalizes `T` scheme-theoretically and acts on `X` by relabelling the coordinates
(`TauCeti.SplitTorus.characterRelabel`). Over a domain these are the only elements of the Weyl
group: if the inverse conjugate of the generic diagonal matrix `diag(t₁, …, t_N)` over `R[X]` is
again diagonal, then, since its entries are distinct, the conjugating matrix is monomial, and its
permutation part determines the character automorphism. So the Weyl group of the diagonal torus
of `GL_N` is the symmetric group on the coordinates, over every domain. This includes `𝔽₂`, where
the group of rational diagonal matrices is trivial, so that the Weyl group is not visible on the
rational points of the torus alone.

Consequently the formal character of every finite-dimensional rational representation of `GL_N`
over a field, restricted to the diagonal torus, is a symmetric Laurent polynomial: it is invariant
under every permutation of the coordinates.

## Main results

* `TauCeti.GeneralLinear.diagonalTorusCoordinateMap_comp_pointConjugationAlgHom_permutationGL`:
  inverse conjugation by a permutation matrix restricts to the diagonal torus as the coordinate
  relabelling.
* `TauCeti.GeneralLinear.characterRelabel_mem_weylGroup_diagonalTorusCoordinateMap`: coordinate
  relabellings lie in the Weyl group of the diagonal torus.
* `TauCeti.GeneralLinear.mem_weylGroup_diagonalTorusCoordinateMap_iff`: over a domain, the Weyl
  group of the diagonal torus consists exactly of the coordinate relabellings.
* `TauCeti.GeneralLinear.permMulEquivDiagonalTorusWeylGroup`: over a domain, the Weyl group of the
  diagonal torus is isomorphic to the symmetric group on the coordinates.
* `TauCeti.GeneralLinear.mapDomain_characterRelabel_formalCharacter`: the formal character of a
  finite-dimensional rational representation of `GL_N` is invariant under permutations of the
  coordinates.

## References

* J. S. Milne, *Algebraic Groups* (2017), Example 19.7 and §21.1.
* J. C. Jantzen, *Representations of Algebraic Groups*, 2nd ed. (2003), Part II, §1.4.
-/

public section

open WithConv

namespace TauCeti.GeneralLinear

universe u v

variable {R : Type u} [CommRing R] {N : ℕ}

/-- The diagonal entries of the generic point of the diagonal torus: the coordinate characters,
as units of the coordinate ring of the torus. -/
private noncomputable def genericDiagonal :
    Fin N → (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)))ˣ := fun i ↦
  SplitTorus.pointsMulEquiv
    (toConv (AlgHom.id R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)))))
    (ULift.up i)

private theorem coe_genericDiagonal (i : Fin N) :
    (genericDiagonal (R := R) i : MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) =
      MonoidAlgebra.single (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) 1 := by
  simp [genericDiagonal, SplitTorus.pointsMulEquiv_apply_coe]

/-- Over a nontrivial ring the coordinate characters are distinct. -/
private theorem genericDiagonal_injective [Nontrivial R] :
    Function.Injective (genericDiagonal (R := R) (N := N)) := by
  intro i j hij
  have hc := congrArg Units.val hij
  rw [coe_genericDiagonal, coe_genericDiagonal] at hc
  have := MonoidAlgebra.single_left_injective (R := R) one_ne_zero hc
  simpa using Finsupp.single_left_injective one_ne_zero (Multiplicative.ofAdd.injective this)

/-- The diagonal entries of the generic point of the diagonal torus, mapped along the coordinate
map of a character automorphism `w`. -/
private noncomputable def mapGenericDiagonal
    (w : Multiplicative (ULift.{u} (Fin N) →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin N) →₀ ℤ)) :
    Fin N → (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)))ˣ := fun i ↦
  Units.map (MonoidAlgebra.domCongr R R w :
    MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ)) →*
      MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) (genericDiagonal i)

private theorem coe_mapGenericDiagonal
    (w : Multiplicative (ULift.{u} (Fin N) →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin N) →₀ ℤ))
    (i : Fin N) :
    (mapGenericDiagonal (R := R) w i : MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) =
      MonoidAlgebra.single (w (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1))) 1 := by
  simp [mapGenericDiagonal, coe_genericDiagonal]

/-- The generic point of the diagonal torus, read as a matrix over the coordinate ring of the
torus, is the diagonal matrix of the coordinate characters. -/
private theorem pointsMulEquiv_toConv_diagonalTorusCoordinateMap :
    pointsMulEquiv N
        (toConv (diagonalTorusCoordinateMap (R := R) (N := N)).hom.toAlgHom) =
      diagGL genericDiagonal := by
  have h := mapPointsFunctor_diagonalTorusCoordinateMap_app (R := R) (N := N)
    (CommAlgCat.of R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))))
    (toConv (AlgHom.id R _))
  rw [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply] at h
  simp only [AlgHom.id_comp] at h
  rw [h, pointsMulEquiv_diagonalTorusPoints]
  congr 1
  funext i
  exact diagonalTorusCoordinates_apply _ i

/-- The generic point of the diagonal torus, followed by the coordinate map of `w`, is the
diagonal matrix of the `w`-images of the coordinate characters. -/
private theorem pointsMulEquiv_toConv_domCongr_comp_diagonalTorusCoordinateMap
    (w : Multiplicative (ULift.{u} (Fin N) →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin N) →₀ ℤ)) :
    pointsMulEquiv N (toConv ((MonoidAlgebra.domCongr R R w).toAlgHom.comp
        (diagonalTorusCoordinateMap (R := R) (N := N)).hom.toAlgHom)) =
      diagGL (mapGenericDiagonal w) := by
  have hmap := pointsMulEquiv_mapValue (R := R) (n := N)
    (MonoidAlgebra.domCongr R R w).toAlgHom
    (toConv (diagonalTorusCoordinateMap (R := R) (N := N)).hom.toAlgHom)
  rw [AlgHom.mapValue_apply, ofConv_toConv] at hmap
  rw [hmap, pointsMulEquiv_toConv_diagonalTorusCoordinateMap, map_diagGL]
  refine congrArg diagGL (funext fun i ↦ Units.ext ?_)
  simp [coe_genericDiagonal, coe_mapGenericDiagonal]

/-- Inverse conjugation by a rational point `g`, evaluated at the generic point of the diagonal
torus, is the generic diagonal matrix conjugated by the inverse of the matrix of `g`. -/
private theorem pointsMulEquiv_toConv_diagonalTorusCoordinateMap_comp_pointConjugationAlgHom
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] R)) :
    pointsMulEquiv N (toConv ((diagonalTorusCoordinateMap (R := R) (N := N)).hom.toAlgHom.comp
        (HopfAlgebra.pointConjugationAlgHom g⁻¹))) =
      Matrix.GeneralLinearGroup.map
          (algebraMap R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))))
          (pointsMulEquiv (R := R) (A := R) N g)⁻¹ *
        diagGL genericDiagonal *
        (Matrix.GeneralLinearGroup.map
          (algebraMap R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))))
          (pointsMulEquiv (R := R) (A := R) N g)⁻¹)⁻¹ := by
  have hg : g⁻¹ = (pointsMulEquiv (R := R) (A := R) N).symm
      (pointsMulEquiv (R := R) (A := R) N g)⁻¹ := by
    rw [map_inv, MulEquiv.symm_apply_apply]
  rw [hg, pointsMulEquiv_toConv_comp_pointConjugationAlgHom,
    pointsMulEquiv_toConv_diagonalTorusCoordinateMap]

/-- **The normalization equation on the generic point.** If inverse conjugation by a rational
point `g` restricts to the diagonal torus as the coordinate map of `w`, then conjugating the
generic diagonal matrix by the inverse of the matrix of `g` gives the diagonal matrix of the
`w`-images of the coordinate characters. -/
private theorem map_inv_mul_diagGL_genericDiagonal_mul_of_comp_eq
    (g : WithConv (coordinateHopfAlgebra R N →ₐ[R] R))
    (w : Multiplicative (ULift.{u} (Fin N) →₀ ℤ) ≃* Multiplicative (ULift.{u} (Fin N) →₀ ℤ))
    (hg : (diagonalTorusCoordinateMap (R := R) (N := N)).hom.toAlgHom.comp
        (HopfAlgebra.pointConjugationAlgHom g⁻¹) =
      (MonoidAlgebra.domCongr R R w).toAlgHom.comp
        (diagonalTorusCoordinateMap (R := R) (N := N)).hom.toAlgHom) :
    Matrix.GeneralLinearGroup.map
          (algebraMap R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))))
          (pointsMulEquiv (R := R) (A := R) N g)⁻¹ *
        diagGL genericDiagonal *
        (Matrix.GeneralLinearGroup.map
          (algebraMap R (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))))
          (pointsMulEquiv (R := R) (A := R) N g)⁻¹)⁻¹ =
      diagGL (mapGenericDiagonal w) := by
  rw [← pointsMulEquiv_toConv_diagonalTorusCoordinateMap_comp_pointConjugationAlgHom, hg,
    pointsMulEquiv_toConv_domCongr_comp_diagonalTorusCoordinateMap]

/-- Relabelling the characters of the diagonal torus along a permutation `σ` of `Fin N` sends
the coordinate character of `i` to that of `σ i`. -/
private theorem characterRelabel_permCongr_single (σ : Equiv.Perm (Fin N)) (i : Fin N) :
    SplitTorus.characterRelabel (Equiv.ulift.{u}.symm.permCongr σ)
        (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) =
      Multiplicative.ofAdd (Finsupp.single (ULift.up (σ i)) 1) := by
  rw [SplitTorus.characterRelabel_ofAdd_single, Equiv.permCongr_apply]
  simp

/-- **Inverse conjugation by a permutation matrix restricts to the diagonal torus as the
coordinate relabelling.** This is the normalization equation, over every commutative ring, for
the permutation matrix of `σ` and the relabelling of the characters of the diagonal torus
along `σ`. -/
theorem diagonalTorusCoordinateMap_comp_pointConjugationAlgHom_permutationGL
    (σ : Equiv.Perm (Fin N)) :
    (diagonalTorusCoordinateMap (R := R) (N := N)).hom.toAlgHom.comp
        (HopfAlgebra.pointConjugationAlgHom
          ((pointsMulEquiv (R := R) (A := R) N).symm (permutationGL σ))⁻¹) =
      (MonoidAlgebra.domCongr R R
          (SplitTorus.characterRelabel (Equiv.ulift.{u}.symm.permCongr σ))).toAlgHom.comp
        (diagonalTorusCoordinateMap (R := R) (N := N)).hom.toAlgHom := by
  apply toConv_injective
  apply (pointsMulEquiv (R := R)
    (A := MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) N).injective
  rw [pointsMulEquiv_toConv_domCongr_comp_diagonalTorusCoordinateMap,
    pointsMulEquiv_toConv_diagonalTorusCoordinateMap_comp_pointConjugationAlgHom,
    MulEquiv.apply_symm_apply, map_inv, map_permutationGL, ← map_inv,
    permutationGL_mul_diagGL_mul_inv]
  congr 1
  funext i
  apply Units.ext
  simp [coe_genericDiagonal, coe_mapGenericDiagonal]

section WeylGroup

variable [ConnectedSpace (PrimeSpectrum R)]

/-- **Coordinate permutations lie in the Weyl group of the diagonal torus of `GL_N`**: the
permutation matrix of `σ` normalizes the diagonal torus scheme-theoretically and acts on its
characters by relabelling the coordinates along `σ`. -/
theorem characterRelabel_mem_weylGroup_diagonalTorusCoordinateMap (σ : Equiv.Perm (Fin N)) :
    SplitTorus.characterRelabel (Equiv.ulift.{u}.symm.permCongr σ) ∈
      BialgHom.weylGroup (diagonalTorusCoordinateMap (R := R) (N := N)).hom
        (diagonalTorusCoordinateMap_surjective R N) :=
  (BialgHom.mem_weylGroup_iff _ _).mpr
    ⟨_, diagonalTorusCoordinateMap_comp_pointConjugationAlgHom_permutationGL σ⟩

/-- The coordinate relabellings, as a homomorphism from the symmetric group on the coordinates
into the Weyl group of the diagonal torus of `GL_N`. -/
noncomputable def permToDiagonalTorusWeylGroup :
    Equiv.Perm (Fin N) →* BialgHom.weylGroup (diagonalTorusCoordinateMap (R := R) (N := N)).hom
      (diagonalTorusCoordinateMap_surjective R N) where
  toFun σ := ⟨SplitTorus.characterRelabel (Equiv.ulift.{u}.symm.permCongr σ),
    characterRelabel_mem_weylGroup_diagonalTorusCoordinateMap σ⟩
  map_one' := Subtype.ext <| MulEquiv.ext fun x ↦ by
    simp only [Equiv.Perm.one_def, Equiv.permCongr_refl]
    exact DFunLike.congr_fun (SplitTorus.characterRelabel_one (sigma := ULift.{u} (Fin N))) x
  map_mul' σ ρ := Subtype.ext <| MulEquiv.ext fun x ↦ by
    simp only [Equiv.permCongr_mul]
    exact (DFunLike.congr_fun (SplitTorus.characterRelabel_comp _ _) x).symm

/-- The relabelling attached to `σ` is the character relabelling along `σ`. -/
@[simp]
theorem coe_permToDiagonalTorusWeylGroup_apply (σ : Equiv.Perm (Fin N)) :
    (permToDiagonalTorusWeylGroup (R := R) σ :
        MulAut (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) =
      SplitTorus.characterRelabel (Equiv.ulift.{u}.symm.permCongr σ) :=
  (rfl)

/-- The homomorphism from coordinate permutations to the Weyl group is injective. -/
theorem permToDiagonalTorusWeylGroup_injective :
    Function.Injective (permToDiagonalTorusWeylGroup (R := R) (N := N)) := by
  intro σ ρ hσρ
  refine Equiv.ext fun i ↦ ?_
  have hi := DFunLike.congr_fun (congrArg Subtype.val hσρ)
    (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1))
  rw [coe_permToDiagonalTorusWeylGroup_apply, coe_permToDiagonalTorusWeylGroup_apply,
    characterRelabel_permCongr_single, characterRelabel_permCongr_single] at hi
  simpa using Finsupp.single_left_injective one_ne_zero (Multiplicative.ofAdd.injective hi)

end WeylGroup

section Domain

variable [IsDomain R]

/-- Over a domain, **every element of the Weyl group of the diagonal torus of `GL_N` is a
coordinate relabelling**: it is the relabelling of the characters along some permutation of
`Fin N`. -/
theorem exists_characterRelabel_eq_of_mem_weylGroup_diagonalTorusCoordinateMap
    {w : MulAut (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))}
    (hw : w ∈ BialgHom.weylGroup (diagonalTorusCoordinateMap (R := R) (N := N)).hom
      (diagonalTorusCoordinateMap_surjective R N)) :
    ∃ σ : Equiv.Perm (Fin N),
      SplitTorus.characterRelabel (Equiv.ulift.{u}.symm.permCongr σ) = w := by
  obtain ⟨g, hg⟩ := (BialgHom.mem_weylGroup_iff _ _).mp hw
  set h : GL (Fin N) (MonoidAlgebra R (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) :=
    Matrix.GeneralLinearGroup.map (algebraMap R _) (pointsMulEquiv (R := R) (A := R) N g)⁻¹
  have hpt := map_inv_mul_diagGL_genericDiagonal_mul_of_comp_eq g w hg
  -- Conjugation by `h` keeps the generic diagonal matrix, whose entries are distinct, diagonal,
  -- so `h` is monomial.
  obtain ⟨d, ρ, hdρ⟩ := exists_eq_diagGL_mul_permutationGL_of_forall_ne (g := h)
    fun i j hij ↦ ⟨genericDiagonal, by
      rw [hpt]
      exact mem_diagonalTorus_iff_exists_diagGL.mpr ⟨_, rfl⟩,
      genericDiagonal_injective.ne hij⟩
  -- Its diagonal factor commutes with the generic diagonal matrix; its permutation factor
  -- relabels the entries.
  have hconj : h * diagGL genericDiagonal * h⁻¹ = diagGL fun i ↦ genericDiagonal (ρ⁻¹ i) := by
    rw [hdρ, mul_inv_rev, show diagGL d * permutationGL ρ * diagGL genericDiagonal *
        ((permutationGL ρ)⁻¹ * (diagGL d)⁻¹) =
        diagGL d * (permutationGL ρ * diagGL genericDiagonal * (permutationGL ρ)⁻¹) *
          (diagGL d)⁻¹ by group,
      permutationGL_mul_diagGL_mul_inv, ← map_inv, ← map_mul, ← map_mul, mul_comm d,
      mul_inv_cancel_right]
  -- Comparing diagonal entries, `w` sends the coordinate character of `i` to that of `ρ⁻¹ i`.
  have hent (i : Fin N) : w (Multiplicative.ofAdd (Finsupp.single (ULift.up i) 1)) =
      Multiplicative.ofAdd (Finsupp.single (ULift.up (ρ⁻¹ i)) 1) := by
    have hi := congrArg Units.val (congrFun (diagGL_injective (hconj.symm.trans hpt)) i)
    rw [coe_genericDiagonal, coe_mapGenericDiagonal] at hi
    exact (MonoidAlgebra.single_left_injective (R := R) one_ne_zero hi).symm
  -- The coordinate characters generate the character lattice.
  refine ⟨ρ⁻¹, MulEquiv.ext fun x ↦ ?_⟩
  obtain ⟨f, rfl⟩ : ∃ f, Multiplicative.ofAdd f = x := ⟨x.toAdd, rfl⟩
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f₁ f₂ h₁ h₂ => rw [ofAdd_add, map_mul, map_mul, h₁, h₂]
  | single a n =>
    obtain ⟨i⟩ := a
    rw [← Finsupp.smul_single_one, ofAdd_zsmul, map_zpow, map_zpow,
      characterRelabel_permCongr_single, hent]

/-- Over a domain, **the Weyl group of the diagonal torus of `GL_N` consists exactly of the
coordinate relabellings.** -/
theorem mem_weylGroup_diagonalTorusCoordinateMap_iff
    {w : MulAut (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))} :
    w ∈ BialgHom.weylGroup (diagonalTorusCoordinateMap (R := R) (N := N)).hom
        (diagonalTorusCoordinateMap_surjective R N) ↔
      ∃ σ : Equiv.Perm (Fin N),
        SplitTorus.characterRelabel (Equiv.ulift.{u}.symm.permCongr σ) = w := by
  refine ⟨exists_characterRelabel_eq_of_mem_weylGroup_diagonalTorusCoordinateMap, ?_⟩
  rintro ⟨σ, rfl⟩
  exact characterRelabel_mem_weylGroup_diagonalTorusCoordinateMap σ

/-- Over a domain, **the Weyl group of the diagonal torus of `GL_N` is the symmetric group**
on the coordinates: a permutation `σ` of `Fin N` corresponds to the relabelling of the characters
along `σ`, induced by the permutation matrix of `σ`. -/
noncomputable def permMulEquivDiagonalTorusWeylGroup :
    Equiv.Perm (Fin N) ≃* BialgHom.weylGroup (diagonalTorusCoordinateMap (R := R) (N := N)).hom
      (diagonalTorusCoordinateMap_surjective R N) :=
  MulEquiv.ofBijective permToDiagonalTorusWeylGroup
    ⟨permToDiagonalTorusWeylGroup_injective, fun w ↦ by
      obtain ⟨σ, hσ⟩ :=
        exists_characterRelabel_eq_of_mem_weylGroup_diagonalTorusCoordinateMap w.property
      exact ⟨σ, Subtype.ext hσ⟩⟩

/-- The isomorphism with the symmetric group sends `σ` to the relabelling along `σ`. -/
@[simp]
theorem permMulEquivDiagonalTorusWeylGroup_apply (σ : Equiv.Perm (Fin N)) :
    permMulEquivDiagonalTorusWeylGroup (R := R) σ = permToDiagonalTorusWeylGroup σ :=
  MulEquiv.ofBijective_apply _ _ σ

end Domain

section FormalCharacter

variable {k : Type u} [Field k] (V : Type v) [AddCommGroup V] [Module k V]
  [Comodule k (coordinateHopfAlgebra k N) V] [FiniteDimensional k V]

/-- **Formal characters of rational representations of `GL_N` are symmetric.** Restricted to the
diagonal torus, the formal character of a finite-dimensional rational representation of `GL_N`
over a field is invariant under every permutation of the coordinates of the character lattice. -/
theorem mapDomain_characterRelabel_formalCharacter (σ : Equiv.Perm (Fin N)) :
    letI : Comodule k (MonoidAlgebra k (Multiplicative (ULift.{u} (Fin N) →₀ ℤ))) V :=
      Comodule.Corestrict (M := V) (diagonalTorusCoordinateMap (R := k) (N := N)).hom.toCoalgHom
    MonoidAlgebra.mapDomain (SplitTorus.characterRelabel (Equiv.ulift.{u}.symm.permCongr σ))
        (Comodule.formalCharacter k _ V) =
      Comodule.formalCharacter k _ V :=
  BialgHom.mapDomain_formalCharacter_of_mem_weylGroup _ (diagonalTorusCoordinateMap_surjective k N)
    V (characterRelabel_mem_weylGroup_diagonalTorusCoordinateMap σ)

end FormalCharacter

end TauCeti.GeneralLinear

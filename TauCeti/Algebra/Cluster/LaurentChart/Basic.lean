/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.MvPolynomial.Laurent.Polynomial
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.RingTheory.AlgebraicIndependent.Basic
public import Mathlib.Algebra.Ring.Hom.InjSurj

/-!
# Faithful Laurent charts

A Laurent chart is an injective algebra map from a multivariable Laurent algebra into a
commutative algebra over a commutative semiring.
Its coordinates are units. Over commutative rings they are algebraically independent, and
every algebraically independent family of units gives a unique chart. A chart need not generate
its ambient algebra, so faithful charts in larger rational function algebras remain available.

The image of a chart is an algebra isomorphic to the Laurent ring. The inverse is its Laurent
expansion, whose finitely supported coefficients are uniquely determined by the chart.
Injective ambient algebra maps and coordinate subfamilies transport these expansions.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, §§2–3.
-/

public section

namespace TauCeti

/-- An injective Laurent algebra map into a commutative algebra. No generation hypothesis is
part of the chart. -/
structure LaurentChart (R K F : Type*) [CommSemiring R] [CommSemiring F] [Algebra R F] where
  /-- The Laurent evaluation map. -/
  toAlgHom : LaurentRing R K →ₐ[R] F
  /-- Faithfulness of Laurent evaluation. -/
  injective : Function.Injective toAlgHom

namespace LaurentChart

variable {R K K' K'' F G H : Type*}

section Semiring
variable [CommSemiring R] [CommSemiring F] [Algebra R F]
  [CommSemiring G] [Algebra R G] [CommSemiring H] [Algebra R H]

instance : FunLike (LaurentChart R K F) (LaurentRing R K) F where
  coe c := c.toAlgHom
  coe_injective c d h := by
    cases c
    cases d
    congr 1
    exact DFunLike.coe_injective h

instance : EmbeddingLike (LaurentChart R K F) (LaurentRing R K) F where
  injective' c := c.injective

@[simp]
theorem coe_toAlgHom (c : LaurentChart R K F) : ⇑c.toAlgHom = c := (rfl)

@[simp]
theorem coe_mk (f : LaurentRing R K →ₐ[R] F) (hf : Function.Injective f) :
    ⇑(LaurentChart.mk f hf) = f := (rfl)

/-- Evaluating a chart constructor applies its given algebra homomorphism. -/
@[simp]
theorem mk_apply (f : LaurentRing R K →ₐ[R] F) (hf : Function.Injective f)
    (p : LaurentRing R K) : LaurentChart.mk f hf p = f p := (rfl)

instance : AlgHomClass (LaurentChart R K F) R (LaurentRing R K) F where
  map_one c := c.toAlgHom.map_one
  map_mul c := c.toAlgHom.map_mul
  map_zero c := c.toAlgHom.map_zero
  map_add c := c.toAlgHom.map_add
  commutes c := c.toAlgHom.commutes

@[simp]
theorem toAlgHom_apply (c : LaurentChart R K F) (p : LaurentRing R K) : c.toAlgHom p = c p :=
  (rfl)

/-- The coordinate of a chart is the image of the corresponding Laurent variable. -/
noncomputable def coordinate (c : LaurentChart R K F) (i : K) : F := c (LaurentRing.X i)

/-- A coordinate is evaluated at its Laurent variable. -/
theorem coordinate_def (c : LaurentChart R K F) (i : K) :
    c.coordinate i = c (LaurentRing.X i) := (rfl)

@[simp]
theorem apply_X (c : LaurentChart R K F) (i : K) : c (LaurentRing.X i) = c.coordinate i :=
  (rfl)

/-- The coordinate of a chart constructor is evaluation at the Laurent variable. -/
@[simp]
theorem coordinate_mk (f : LaurentRing R K →ₐ[R] F) (hf : Function.Injective f) (i : K) :
    (LaurentChart.mk f hf).coordinate i = f (LaurentRing.X i) := (rfl)

/-- A chart is determined by its values on the Laurent variables. -/
@[ext]
theorem ext {c d : LaurentChart R K F} (h : ∀ i, c.coordinate i = d.coordinate i) : c = d := by
  apply DFunLike.ext
  intro p
  exact DFunLike.congr_fun (LaurentRing.algHom_ext h) p

/-- Coordinates of a Laurent chart are units, including when the chart is not generating. -/
noncomputable def coordinateUnit (c : LaurentChart R K F) : K → Fˣ :=
  LaurentRing.aevalEquiv.symm c.toAlgHom

/-- Coordinate units are recovered from the chart's Laurent evaluation homomorphism. -/
theorem coordinateUnit_def (c : LaurentChart R K F) :
    c.coordinateUnit = LaurentRing.aevalEquiv.symm c.toAlgHom := (rfl)

@[simp]
theorem coordinateUnit_mk (f : LaurentRing R K →ₐ[R] F) (hf : Function.Injective f) :
    (LaurentChart.mk f hf).coordinateUnit = LaurentRing.aevalEquiv.symm f := (rfl)

@[simp]
theorem val_coordinateUnit (c : LaurentChart R K F) (i : K) :
    (c.coordinateUnit i : F) = c.coordinate i := by
  exact LaurentRing.val_aevalEquiv_symm_apply c.toAlgHom i

@[simp]
theorem coordinate_ne_zero [Nontrivial F] (c : LaurentChart R K F) (i : K) : c.coordinate i ≠ 0 :=
  by
  rw [← c.val_coordinateUnit]
  exact Units.ne_zero _

/-- Evaluating at the coordinate units recovers the whole chart, not only its variables. -/
@[simp]
theorem aeval_coordinateUnit (c : LaurentChart R K F) :
    LaurentRing.aeval c.coordinateUnit = c.toAlgHom :=
  LaurentRing.aeval_aevalEquiv_symm c.toAlgHom

/-- A Laurent monomial evaluates as the product of the prescribed integer coordinate powers. -/
theorem apply_single (c : LaurentChart R K F) (m : K →₀ ℤ) (r : R) :
    c (AddMonoidAlgebra.single m r) =
      r • ((m.prod (fun i n ↦ c.coordinateUnit i ^ n) : Fˣ) : F) := by
  rw [← toAlgHom_apply, ← aeval_coordinateUnit]
  exact LaurentRing.aeval_single c.coordinateUnit m r

/-- Evaluating the negative standard-basis monomial gives the inverse coordinate. -/
@[simp high]
theorem apply_single_neg_single_one (c : LaurentChart R K F) (i : K) :
    c (AddMonoidAlgebra.single (-Finsupp.single i 1) 1) = (((c.coordinateUnit i)⁻¹ : Fˣ) : F) := by
  rw [← Finsupp.single_neg, apply_single]
  simp only [Finsupp.prod_single_index, zpow_zero, one_smul, zpow_neg_one]

/-- On polynomials the chart is evaluation at its coordinate family. -/
theorem comp_toLaurent (c : LaurentChart R K F) :
    c.toAlgHom.comp MvPolynomial.toLaurent = MvPolynomial.aeval c.coordinate := by
  apply MvPolynomial.algHom_ext
  intro i
  simp [coordinate, -apply_X]

/-- Evaluate an ordinary polynomial using the coordinates of a Laurent chart. -/
theorem apply_toLaurent (c : LaurentChart R K F) (p : MvPolynomial K R) :
    c (MvPolynomial.toLaurent p) = MvPolynomial.aeval c.coordinate p :=
  DFunLike.congr_fun c.comp_toLaurent p

/-- Faithfulness into a domain forces the coefficient semiring to be a domain. -/
theorem isDomain [IsDomain F] (c : LaurentChart R K F) : IsDomain R := by
  apply Function.Injective.isDomain (algebraMap R F)
  intro x y h
  apply MvPolynomial.C_injective K R
  apply MvPolynomial.toLaurent_injective
  apply c.injective
  simpa only [← MvPolynomial.algebraMap_eq, AlgHom.commutes] using h

end Semiring

section RingCoordinates
variable [CommRing R] [CommRing F] [Algebra R F]

/-- The coordinates of a faithful Laurent chart are algebraically independent. -/
theorem algebraicIndependent (c : LaurentChart R K F) : AlgebraicIndependent R c.coordinate := by
  have hc : Function.Injective (LaurentRing.aeval (R := R) c.coordinateUnit) := by
    rw [aeval_coordinateUnit]
    exact c.injective
  simpa only [val_coordinateUnit] using
    (LaurentRing.aeval_injective_iff_algebraicIndependent c.coordinateUnit).mp hc

/-- An algebraically independent family of units determines a faithful Laurent chart. -/
noncomputable def ofCoordinates (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) : LaurentChart R K F where
  toAlgHom := LaurentRing.aeval x
  injective := (LaurentRing.aeval_injective_iff_algebraicIndependent x).mpr hx

@[simp]
theorem toAlgHom_ofCoordinates (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) :
    (ofCoordinates x hx).toAlgHom = LaurentRing.aeval x := (rfl)

@[simp]
theorem ofCoordinates_apply (x : K → Fˣ) (hx : AlgebraicIndependent R fun i ↦ (x i : F))
    (p : LaurentRing R K) : ofCoordinates x hx p = LaurentRing.aeval x p := (rfl)

@[simp]
theorem coordinate_ofCoordinates (x : K → Fˣ) (hx : AlgebraicIndependent R fun i ↦ (x i : F))
    (i : K) : (ofCoordinates x hx).coordinate i = x i := by
  simp [coordinate, -apply_X]

@[simp]
theorem coordinateUnit_ofCoordinates (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) : (ofCoordinates x hx).coordinateUnit = x :=
  LaurentRing.aevalEquiv_symm_aeval x

@[simp]
theorem ofCoordinates_coordinateUnit (c : LaurentChart R K F) :
    ofCoordinates c.coordinateUnit (by simpa using c.algebraicIndependent) = c := by
  ext i
  simp

/-- Laurent charts are precisely algebraically independent families of units. -/
noncomputable def coordinatesEquiv :
    LaurentChart R K F ≃ {x : K → Fˣ // AlgebraicIndependent R fun i ↦ (x i : F)} where
  toFun c := ⟨c.coordinateUnit, by simpa using c.algebraicIndependent⟩
  invFun x := ofCoordinates x.1 x.2
  left_inv := ofCoordinates_coordinateUnit
  right_inv x := Subtype.ext (coordinateUnit_ofCoordinates x.1 x.2)

@[simp]
theorem val_coordinatesEquiv_apply (c : LaurentChart R K F) :
    (coordinatesEquiv c).1 = c.coordinateUnit := (rfl)

@[simp]
theorem coordinatesEquiv_symm_apply
    (x : {x : K → Fˣ // AlgebraicIndependent R fun i ↦ (x i : F)}) :
    coordinatesEquiv.symm x = ofCoordinates x.1 x.2 := (rfl)

/-- Taking the coordinates of a chart constructed from units recovers the unit family. -/
@[simp]
theorem coordinatesEquiv_ofCoordinates (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) :
    coordinatesEquiv (ofCoordinates x hx) = ⟨x, hx⟩ :=
  Subtype.ext (coordinateUnit_ofCoordinates x hx)

end RingCoordinates

section Semiring
variable [CommSemiring R] [CommSemiring F] [Algebra R F]
  [CommSemiring G] [Algebra R G] [CommSemiring H] [Algebra R H]

/-! ### Ambient embeddings and coordinate subfamilies -/

/-- Transport a chart along an embedding of ambient algebras. -/
noncomputable def map (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) :
  LaurentChart R K G where
  toAlgHom := f.comp c.toAlgHom
  injective := hf.comp c.injective

@[simp]
theorem toAlgHom_map (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) :
    (c.map f hf).toAlgHom = f.comp c.toAlgHom := (rfl)

@[simp]
theorem map_apply (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) (p :
  LaurentRing R K) :
    c.map f hf p = f (c p) := (rfl)

@[simp]
theorem coordinate_map (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) (i :
  K) :
    (c.map f hf).coordinate i = f (c.coordinate i) := (rfl)

@[simp]
theorem coordinateUnit_map (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) (i
  : K) :
    (c.map f hf).coordinateUnit i = Units.map (f : F →* G) (c.coordinateUnit i) := by
  apply Units.ext
  simp

@[simp]
theorem map_id (c : LaurentChart R K F) : c.map (AlgHom.id R F) Function.injective_id = c := by
  ext i
  rfl

@[simp]
theorem map_map (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) (g : G →ₐ[R]
  H) (hg : Function.Injective g) :
    (c.map f hf).map g hg = c.map (g.comp f) (hg.comp hf) := by
  ext i
  rfl

/-- A subfamily of the coordinates gives a faithful chart in the same ambient algebra. -/
noncomputable def restrict (c : LaurentChart R K F) (f : K' ↪ K) : LaurentChart R K' F where
  toAlgHom := c.toAlgHom.comp (LaurentRing.rename f)
  injective := c.injective.comp (LaurentRing.rename_injective f.injective)

@[simp]
theorem toAlgHom_restrict (c : LaurentChart R K F) (f : K' ↪ K) :
    (c.restrict f).toAlgHom = c.toAlgHom.comp (LaurentRing.rename f) := (rfl)

@[simp]
theorem restrict_apply (c : LaurentChart R K F) (f : K' ↪ K) (p : LaurentRing R K') :
    c.restrict f p = c (LaurentRing.rename f p) := (rfl)

@[simp]
theorem coordinate_restrict (c : LaurentChart R K F) (f : K' ↪ K) (i : K') :
    (c.restrict f).coordinate i = c.coordinate (f i) := by
  simp [coordinate, -apply_X]

@[simp]
theorem coordinateUnit_restrict (c : LaurentChart R K F) (f : K' ↪ K) (i : K') :
    (c.restrict f).coordinateUnit i = c.coordinateUnit (f i) := by
  apply Units.ext
  simp

@[simp]
theorem restrict_refl (c : LaurentChart R K F) : c.restrict (Function.Embedding.refl K) = c := by
  ext i
  simp

@[simp]
theorem restrict_restrict (c : LaurentChart R K F) (f : K' ↪ K) (g : K'' ↪ K') :
    (c.restrict f).restrict g = c.restrict (g.trans f) := by
  ext i
  simp

@[simp]
theorem map_restrict (c : LaurentChart R K F) (f : K' ↪ K) (φ : F →ₐ[R] G) (hφ :
  Function.Injective φ) :
    (c.restrict f).map φ hφ = (c.map φ hφ).restrict f := by
  ext i
  simp

/-- Reindexing is restriction along the inverse equivalence. -/
noncomputable def reindex (c : LaurentChart R K F) (e : K ≃ K') : LaurentChart R K' F :=
  c.restrict e.symm.toEmbedding

@[simp]
theorem toAlgHom_reindex (c : LaurentChart R K F) (e : K ≃ K') :
    (c.reindex e).toAlgHom = c.toAlgHom.comp (LaurentRing.rename e.symm) := (rfl)

@[simp]
theorem reindex_apply (c : LaurentChart R K F) (e : K ≃ K') (p : LaurentRing R K') :
    c.reindex e p = c (LaurentRing.rename e.symm p) := (rfl)

@[simp]
theorem coordinate_reindex (c : LaurentChart R K F) (e : K ≃ K') (i : K') :
    (c.reindex e).coordinate i = c.coordinate (e.symm i) := by
  simp [reindex]

@[simp]
theorem coordinateUnit_reindex (c : LaurentChart R K F) (e : K ≃ K') (i : K') :
    (c.reindex e).coordinateUnit i = c.coordinateUnit (e.symm i) := by
  simp [reindex]

@[simp]
theorem reindex_refl (c : LaurentChart R K F) : c.reindex (Equiv.refl K) = c := by
  simp [reindex]

@[simp]
theorem reindex_trans (c : LaurentChart R K F) (e : K ≃ K') (e' : K' ≃ K'') :
    (c.reindex e).reindex e' = c.reindex (e.trans e') := by
  ext i
  simp

@[simp]
theorem map_reindex (c : LaurentChart R K F) (e : K ≃ K') (φ : F →ₐ[R] G) (hφ : Function.Injective
  φ) :
    (c.reindex e).map φ hφ = (c.map φ hφ).reindex e := by
  simp [reindex]

/-- The Laurent subalgebra realized by a chart. -/
noncomputable def range (c : LaurentChart R K F) : Subalgebra R F := c.toAlgHom.range

/-- The chart range is the image of its evaluation homomorphism. -/
theorem range_def (c : LaurentChart R K F) : c.range = c.toAlgHom.range := (rfl)

/-- Membership in the Laurent subalgebra is existence of a Laurent representative. -/
theorem mem_range (c : LaurentChart R K F) (z : F) :
    z ∈ c.range ↔ ∃ p : LaurentRing R K, c p = z := Iff.rfl

@[simp]
theorem apply_mem_range (c : LaurentChart R K F) (p : LaurentRing R K) :
    c p ∈ c.range := ⟨p, rfl⟩

/-- The range of a mapped chart is the ambient map of the original range. -/
theorem range_map (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) :
    (c.map f hf).range = c.range.map f := by
  exact AlgHom.range_comp c.toAlgHom f

/-- Restricting the coordinates restricts the chart range. -/
theorem range_restrict_le (c : LaurentChart R K F) (f : K' ↪ K) :
    (c.restrict f).range ≤ c.range := by
  rintro _ ⟨p, rfl⟩
  exact ⟨LaurentRing.rename f p, rfl⟩

@[simp]
theorem set_range_reindex (c : LaurentChart R K F) (e : K ≃ K') :
    Set.range (c.reindex e) = Set.range c :=
  by
    calc
      Set.range (c.reindex e) =
          Set.range (c ∘ LaurentRing.renameEquiv R e.symm) := by
        congr 1
        funext p
        simp
      _ = Set.range c := EquivLike.range_comp c (LaurentRing.renameEquiv R e.symm)

@[simp↓]
theorem range_reindex (c : LaurentChart R K F) (e : K ≃ K') :
    (c.reindex e).range = c.range := by
  exact SetLike.coe_injective (c.set_range_reindex e)

/-- A coordinate lies in the image of its chart. -/
@[simp]
theorem coordinate_mem_range (c : LaurentChart R K F) (i : K) :
    c.coordinate i ∈ c.range := ⟨LaurentRing.X i, c.apply_X i⟩

/-- The inverse unit coordinate lies in the image of its chart. -/
@[simp]
theorem inv_coordinateUnit_mem_range (c : LaurentChart R K F) (i : K) :
    (((c.coordinateUnit i)⁻¹ : Fˣ) : F) ∈ c.range :=
  ⟨AddMonoidAlgebra.single (-Finsupp.single i 1) 1, c.apply_single_neg_single_one i⟩

/-- The range is generated as an algebra by the coordinates and their inverses. -/
theorem range_eq_adjoin (c : LaurentChart R K F) :
    c.range = Algebra.adjoin R
      (Set.range c.coordinate ∪ Set.range fun i ↦ (((c.coordinateUnit i)⁻¹ : Fˣ) : F)) := by
  apply le_antisymm
  · rintro _ ⟨p, rfl⟩
    simp only [AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, toAlgHom_apply]
    let S := Algebra.adjoin R (Set.range c.coordinate ∪ Set.range fun i ↦ (((c.coordinateUnit i)⁻¹
      : Fˣ) : F))
    have hc (i : K) : c.coordinate i ∈ S :=
      Algebra.subset_adjoin (Set.mem_union_left _ (Set.mem_range_self i))
    have hi (i : K) : (((c.coordinateUnit i)⁻¹ : Fˣ) : F) ∈ S :=
      Algebra.subset_adjoin (Set.mem_union_right _ (Set.mem_range_self i))
    induction p using AddMonoidAlgebra.induction_linear with
    | zero => simp
    | add p q hp hq => simpa using S.add_mem hp hq
    | single m r =>
      rw [apply_single]
      apply S.smul_mem
      simp only [Finsupp.prod, Units.coe_prod]
      apply S.prod_mem
      intro i _
      cases m i with
      | ofNat n => simpa using S.pow_mem (hc i) n
      | negSucc n =>
        simpa only [zpow_negSucc, ← inv_pow, Units.val_pow_eq_pow_val] using
          S.pow_mem (hi i) (n + 1)
  · apply Algebra.adjoin_le
    rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
    · exact c.coordinate_mem_range i
    · exact c.inv_coordinateUnit_mem_range i

/-- Membership in a chart range can be tested in the coordinate-and-inverse algebra. -/
theorem mem_range_iff_adjoin (c : LaurentChart R K F) (z : F) :
    z ∈ c.range ↔ z ∈ Algebra.adjoin R
      (Set.range c.coordinate ∪ Set.range fun i ↦ (((c.coordinateUnit i)⁻¹ : Fˣ) : F)) := by
  rw [range_eq_adjoin]

/-- An ambient algebra embedding reflects chart range membership. -/
@[simp↓]
theorem mem_range_map_iff (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) (z
  : F) :
    f z ∈ (c.map f hf).range ↔ z ∈ c.range := by
  constructor
  · rintro ⟨p, hp⟩
    exact ⟨p, hf (by simpa using hp)⟩
  · rintro ⟨p, rfl⟩
    exact ⟨p, rfl⟩

/-! ### Laurent expansion -/

/-- The unique Laurent expansion of an element in the image of a faithful chart. -/
noncomputable def laurentExpansion (c : LaurentChart R K F) :
    c.range ≃ₐ[R] LaurentRing R K :=
  (AlgEquiv.ofInjective c.toAlgHom c.injective).symm

/-- Evaluating a Laurent expansion returns the element that was expanded. -/
@[simp]
theorem apply_laurentExpansion (c : LaurentChart R K F) (x : c.range) :
    c (c.laurentExpansion x) = x := by
  exact congrArg Subtype.val ((AlgEquiv.ofInjective c.toAlgHom c.injective).apply_symm_apply x)

/-- Expanding an evaluated Laurent polynomial returns that polynomial. -/
@[simp↓]
theorem laurentExpansion_apply (c : LaurentChart R K F) (p : LaurentRing R K) :
    c.laurentExpansion ⟨c p, c.apply_mem_range p⟩ = p :=
  (AlgEquiv.ofInjective c.toAlgHom c.injective).symm_apply_apply p

/-- Expanding a coordinate returns its Laurent variable. -/
@[simp↓]
theorem laurentExpansion_coordinate (c : LaurentChart R K F) (i : K)
    (h : c.coordinate i ∈ c.range) :
    c.laurentExpansion ⟨c.coordinate i, h⟩ = LaurentRing.X i := by
  simpa only [apply_X] using c.laurentExpansion_apply (LaurentRing.X i)

/-- Expanding the inverse of a coordinate returns its negative standard-basis monomial. -/
@[simp↓]
theorem laurentExpansion_inv_coordinateUnit (c : LaurentChart R K F) (i : K)
    (h : (((c.coordinateUnit i)⁻¹ : Fˣ) : F) ∈ c.range) :
    c.laurentExpansion ⟨(((c.coordinateUnit i)⁻¹ : Fˣ) : F), h⟩ =
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 := by
  apply c.injective
  rw [toAlgHom_apply, toAlgHom_apply, apply_laurentExpansion]
  symm
  simpa only [Finsupp.prod_single_index, zpow_zero, one_smul, zpow_neg_one] using
    c.apply_single_neg_single_one i

end Semiring
section RingCoordinates
variable [CommRing R] [CommRing F] [Algebra R F]

/-- Constructor-normal evaluation expands to its complete Laurent polynomial. -/
@[simp↓]
theorem laurentExpansion_ofCoordinates_aeval (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (p : LaurentRing R K)
    (h : LaurentRing.aeval x p ∈ (ofCoordinates x hx).range) :
    (ofCoordinates x hx).laurentExpansion ⟨LaurentRing.aeval x p, h⟩ = p := by
  simpa only [ofCoordinates_apply] using (ofCoordinates x hx).laurentExpansion_apply p

/-- Expand a unit coordinate in the normal form of the coordinate-family constructor. -/
@[simp↓]
theorem laurentExpansion_ofCoordinates_coordinate (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (i : K)
    (h : (x i : F) ∈ (ofCoordinates x hx).range) :
    (ofCoordinates x hx).laurentExpansion ⟨(x i : F), h⟩ = LaurentRing.X i := by
  simpa only [coordinate_ofCoordinates] using
    (ofCoordinates x hx).laurentExpansion_coordinate i
      (by simpa only [coordinate_ofCoordinates] using h)

/-- Expand an inverse unit coordinate in the coordinate-family constructor. -/
@[simp↓]
theorem laurentExpansion_ofCoordinates_inv_coordinateUnit (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (i : K)
    (h : (((x i)⁻¹ : Fˣ) : F) ∈ (ofCoordinates x hx).range) :
    (ofCoordinates x hx).laurentExpansion ⟨(((x i)⁻¹ : Fˣ) : F), h⟩ =
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 := by
  simpa only [coordinateUnit_ofCoordinates] using
    (ofCoordinates x hx).laurentExpansion_inv_coordinateUnit i
      (by simpa only [coordinateUnit_ofCoordinates] using h)

end RingCoordinates
section Semiring
variable [CommSemiring R] [CommSemiring F] [Algebra R F]
  [CommSemiring G] [Algebra R G] [CommSemiring H] [Algebra R H]

/-- Restriction-normal evaluation expands to its complete smaller Laurent polynomial. -/
@[simp↓]
theorem laurentExpansion_restrict_rename (c : LaurentChart R K F) (f : K' ↪ K)
    (p : LaurentRing R K') (h : c (LaurentRing.rename f p) ∈ (c.restrict f).range) :
    (c.restrict f).laurentExpansion ⟨c (LaurentRing.rename f p), h⟩ = p := by
  simpa only [restrict_apply] using (c.restrict f).laurentExpansion_apply p

/-- Expand a retained coordinate in the normal form of a restricted chart. -/
@[simp↓]
theorem laurentExpansion_restrict_coordinate (c : LaurentChart R K F) (f : K' ↪ K) (i : K')
    (h : c.coordinate (f i) ∈ (c.restrict f).range) :
    (c.restrict f).laurentExpansion ⟨c.coordinate (f i), h⟩ = LaurentRing.X i := by
  simpa only [coordinate_restrict] using (c.restrict f).laurentExpansion_coordinate i
    (by simpa only [coordinate_restrict] using h)

/-- Expand the inverse of a retained coordinate in a restricted chart. -/
@[simp↓]
theorem laurentExpansion_restrict_inv_coordinateUnit (c : LaurentChart R K F) (f : K' ↪ K) (i : K')
    (h : (((c.coordinateUnit (f i))⁻¹ : Fˣ) : F) ∈ (c.restrict f).range) :
    (c.restrict f).laurentExpansion ⟨(((c.coordinateUnit (f i))⁻¹ : Fˣ) : F), h⟩ =
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 := by
  simpa only [coordinateUnit_restrict] using (c.restrict f).laurentExpansion_inv_coordinateUnit i
    (by simpa only [coordinateUnit_restrict] using h)

/-- Expansion can be recognized by equality after faithful chart evaluation. -/
theorem laurentExpansion_eq_iff (c : LaurentChart R K F) (x : c.range)
    (p : LaurentRing R K) : c.laurentExpansion x = p ↔ (x : F) = c p := by
  rw [← c.injective.eq_iff]
  simp

/-- The finitely supported Laurent coefficients of an element in a chart image. -/
noncomputable def coeff (c : LaurentChart R K F) :
    c.range ≃ₗ[R] ((K →₀ ℤ) →₀ R) :=
  c.laurentExpansion.toLinearEquiv.trans (AddMonoidAlgebra.coeffLinearEquiv R)

/-- The finite coefficient data is the coefficient function of the Laurent expansion. -/
theorem coeff_def (c : LaurentChart R K F) (x : c.range) :
    c.coeff x = (c.laurentExpansion x).coeff := (rfl)

@[simp]
theorem coe_laurentExpansion_symm_apply (c : LaurentChart R K F) (p : LaurentRing R K) :
    ((c.laurentExpansion.symm p : c.range) : F) = c p := (rfl)

@[simp↓]
theorem coeff_apply (c : LaurentChart R K F) (p : LaurentRing R K) :
    c.coeff ⟨c p, c.apply_mem_range p⟩ = p.coeff := by
  simp [coeff]

/-- A coordinate has its single standard-basis coefficient. -/
@[simp↓]
theorem coeff_coordinate (c : LaurentChart R K F) (i : K)
    (h : c.coordinate i ∈ c.range) :
    c.coeff ⟨c.coordinate i, h⟩ = Finsupp.single (Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_coordinate, LaurentRing.X_def, AddMonoidAlgebra.coeff_single]

/-- An inverse coordinate has its single negative standard-basis coefficient. -/
@[simp↓]
theorem coeff_inv_coordinateUnit (c : LaurentChart R K F) (i : K)
    (h : (((c.coordinateUnit i)⁻¹ : Fˣ) : F) ∈ c.range) :
    c.coeff ⟨(((c.coordinateUnit i)⁻¹ : Fˣ) : F), h⟩ = Finsupp.single (-Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_inv_coordinateUnit, AddMonoidAlgebra.coeff_single]

/-- The coefficient data of the unit consists of the constant monomial with coefficient one. -/
@[simp]
theorem coeff_one (c : LaurentChart R K F) : c.coeff 1 = Finsupp.single 0 1 := by
  rw [coeff_def, map_one, AddMonoidAlgebra.one_def, AddMonoidAlgebra.coeff_single]

end Semiring
section RingCoordinates
variable [CommRing R] [CommRing F] [Algebra R F]

/-- Coefficients recover a constructor-normal Laurent evaluation. -/
@[simp↓]
theorem coeff_ofCoordinates_aeval (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (p : LaurentRing R K)
    (h : LaurentRing.aeval x p ∈ (ofCoordinates x hx).range) :
    (ofCoordinates x hx).coeff ⟨LaurentRing.aeval x p, h⟩ = p.coeff := by
  rw [coeff_def, laurentExpansion_ofCoordinates_aeval]

/-- Coefficients at a unit coordinate in the coordinate-family constructor. -/
@[simp↓]
theorem coeff_ofCoordinates_coordinate (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (i : K)
    (h : (x i : F) ∈ (ofCoordinates x hx).range) :
    (ofCoordinates x hx).coeff ⟨(x i : F), h⟩ = Finsupp.single (Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_ofCoordinates_coordinate, LaurentRing.X_def,
    AddMonoidAlgebra.coeff_single]

/-- Coefficients at an inverse unit coordinate in the coordinate-family constructor. -/
@[simp↓]
theorem coeff_ofCoordinates_inv_coordinateUnit (x : K → Fˣ)
    (hx : AlgebraicIndependent R fun i ↦ (x i : F)) (i : K)
    (h : (((x i)⁻¹ : Fˣ) : F) ∈ (ofCoordinates x hx).range) :
    (ofCoordinates x hx).coeff ⟨(((x i)⁻¹ : Fˣ) : F), h⟩ = Finsupp.single (-Finsupp.single i 1) 1
      := by
  rw [coeff_def, laurentExpansion_ofCoordinates_inv_coordinateUnit, AddMonoidAlgebra.coeff_single]

end RingCoordinates
section Semiring
variable [CommSemiring R] [CommSemiring F] [Algebra R F]
  [CommSemiring G] [Algebra R G] [CommSemiring H] [Algebra R H]

/-- Coefficients recover restriction-normal evaluation. -/
@[simp↓]
theorem coeff_restrict_rename (c : LaurentChart R K F) (f : K' ↪ K)
    (p : LaurentRing R K') (h : c (LaurentRing.rename f p) ∈ (c.restrict f).range) :
    (c.restrict f).coeff ⟨c (LaurentRing.rename f p), h⟩ = p.coeff := by
  rw [coeff_def, laurentExpansion_restrict_rename]

/-- Coefficients at a retained coordinate of a restricted chart. -/
@[simp↓]
theorem coeff_restrict_coordinate (c : LaurentChart R K F) (f : K' ↪ K) (i : K')
    (h : c.coordinate (f i) ∈ (c.restrict f).range) :
    (c.restrict f).coeff ⟨c.coordinate (f i), h⟩ = Finsupp.single (Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_restrict_coordinate, LaurentRing.X_def,
    AddMonoidAlgebra.coeff_single]

/-- Coefficients at the inverse of a retained coordinate in a restricted chart. -/
@[simp↓]
theorem coeff_restrict_inv_coordinateUnit (c : LaurentChart R K F) (f : K' ↪ K) (i : K')
    (h : (((c.coordinateUnit (f i))⁻¹ : Fˣ) : F) ∈ (c.restrict f).range) :
    (c.restrict f).coeff ⟨(((c.coordinateUnit (f i))⁻¹ : Fˣ) : F), h⟩ =
      Finsupp.single (-Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_restrict_inv_coordinateUnit, AddMonoidAlgebra.coeff_single]

/-- Inverting the coefficient equivalence reconstructs the Laurent polynomial with that data. -/
@[simp]
theorem laurentExpansion_coeff_symm_apply (c : LaurentChart R K F) (g : (K →₀ ℤ) →₀ R) :
    c.laurentExpansion (c.coeff.symm g) = AddMonoidAlgebra.ofCoeff g := by
  apply AddMonoidAlgebra.coeff_injective
  rw [← coeff_def, LinearEquiv.apply_symm_apply, AddMonoidAlgebra.coeff_ofCoeff]

/-- The inverse coefficient equivalence evaluates the finite sum of its Laurent monomials. -/
@[simp]
theorem coe_coeff_symm_apply (c : LaurentChart R K F) (g : (K →₀ ℤ) →₀ R) :
    ((c.coeff.symm g : c.range) : F) =
      g.sum (fun m r ↦ c (AddMonoidAlgebra.single m r)) := by
  rw [← c.apply_laurentExpansion (c.coeff.symm g), laurentExpansion_coeff_symm_apply]
  conv_lhs => rw [← AddMonoidAlgebra.sum_coeff_single (AddMonoidAlgebra.ofCoeff g)]
  simp only [Finsupp.sum, map_sum]

/-- The finite Laurent expansion reconstructs the element being expanded. -/
theorem sum_apply_single_coeff (c : LaurentChart R K F) (x : c.range) :
    ∑ m ∈ (c.coeff x).support,
      c (AddMonoidAlgebra.single m (c.coeff x m)) = (x : F) := by
  rw [coeff_def, ← c.apply_laurentExpansion x]
  conv_rhs =>
    rw [← AddMonoidAlgebra.sum_coeff_single (c.laurentExpansion x), Finsupp.sum, map_sum]

/-- Restriction expands a subchart value by renaming its smaller coordinate family. -/
theorem laurentExpansion_restrict (c : LaurentChart R K F) (f : K' ↪ K)
    (x : (c.restrict f).range) :
    c.laurentExpansion ⟨x, c.range_restrict_le f x.property⟩ =
      LaurentRing.rename f ((c.restrict f).laurentExpansion x) := by
  apply c.injective
  simp only [toAlgHom_apply, apply_laurentExpansion, ← restrict_apply]

/-- Coefficients of a restricted chart are transported by the same exponent renaming. -/
theorem coeff_restrict (c : LaurentChart R K F) (f : K' ↪ K)
    (x : (c.restrict f).range) :
    c.coeff ⟨x, c.range_restrict_le f x.property⟩ =
      Finsupp.mapDomain (Finsupp.mapDomain f) ((c.restrict f).coeff x) := by
  rw [coeff_def, laurentExpansion_restrict, LaurentRing.rename_apply,
    AddMonoidAlgebra.coeff_mapDomain, coeff_def]

/-- Restriction preserves the coefficient at every embedded exponent. -/
@[simp]
theorem coeff_restrict_apply (c : LaurentChart R K F) (f : K' ↪ K)
    (x : (c.restrict f).range) (m : K' →₀ ℤ) :
    c.coeff ⟨x, c.range_restrict_le f x.property⟩ (Finsupp.mapDomain f m) =
      (c.restrict f).coeff x m := by
  rw [coeff_restrict]
  exact Finsupp.mapDomain_apply_of_injective (Finsupp.mapDomain_injective f.injective) _ m

/-- Ambient algebra transport gives an equivalence between the two chart ranges. -/
noncomputable def mapRange (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) :
    c.range ≃ₐ[R] (c.map f hf).range :=
  c.laurentExpansion.trans (c.map f hf).laurentExpansion.symm

@[simp]
theorem coe_mapRange_apply (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) (x
  : c.range) :
    ((c.mapRange f hf x : (c.map f hf).range) : G) = f x := by
  simp [mapRange]

/-- Range transport sends a subtype constructor to the embedded element. -/
@[simp]
theorem mapRange_mk (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f) (z : F)
    (h : z ∈ c.range) :
    c.mapRange f hf ⟨z, h⟩ = ⟨f z, (c.mem_range_map_iff f hf z).mpr h⟩ :=
  Subtype.ext (c.coe_mapRange_apply f hf ⟨z, h⟩)

/-- The inverse range transport is characterized by the ambient algebra embedding. -/
@[simp]
theorem map_coe_mapRange_symm_apply (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf :
  Function.Injective f)
    (y : (c.map f hf).range) :
    f ((c.mapRange f hf).symm y : F) = y := by
  rw [← coe_mapRange_apply, AlgEquiv.apply_symm_apply]

/-- Inverse range transport cancels the ambient algebra embedding on arbitrary values. -/
@[simp↓]
theorem mapRange_symm_apply (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f)
  (z : F)
    (h : f z ∈ (c.map f hf).range) :
    (c.mapRange f hf).symm ⟨f z, h⟩ = ⟨z, (c.mem_range_map_iff f hf z).mp h⟩ := by
  apply Subtype.ext
  apply hf
  exact c.map_coe_mapRange_symm_apply f hf ⟨f z, h⟩

/-- Expansion after an ambient embedding, for any element of the transported range. -/
@[simp↓]
theorem laurentExpansion_map (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f)
    (y : (c.map f hf).range) :
    (c.map f hf).laurentExpansion y = c.laurentExpansion ((c.mapRange f hf).symm y) := by
  simp [mapRange]

/-- Laurent coefficients are unchanged by an ambient algebra embedding. -/
@[simp↓]
theorem coeff_map (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f)
    (y : (c.map f hf).range) :
    (c.map f hf).coeff y = c.coeff ((c.mapRange f hf).symm y) := by
  rw [coeff_def, laurentExpansion_map, coeff_def]

/-- Inverting an expansion commutes with ambient range transport. -/
@[simp]
theorem laurentExpansion_map_symm (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf :
  Function.Injective f)
    (p : LaurentRing R K) :
    (c.map f hf).laurentExpansion.symm p = c.mapRange f hf (c.laurentExpansion.symm p) := by
  apply (c.map f hf).laurentExpansion.injective
  rw [AlgEquiv.apply_symm_apply, laurentExpansion_map,
    AlgEquiv.symm_apply_apply, AlgEquiv.apply_symm_apply]

/-- Inverting the coefficient equivalence commutes with ambient range transport. -/
@[simp]
theorem coeff_map_symm (c : LaurentChart R K F) (f : F →ₐ[R] G) (hf : Function.Injective f)
    (g : (K →₀ ℤ) →₀ R) :
    (c.map f hf).coeff.symm g = c.mapRange f hf (c.coeff.symm g) := by
  apply (c.map f hf).coeff.injective
  rw [LinearEquiv.apply_symm_apply, coeff_map,
    AlgEquiv.symm_apply_apply, LinearEquiv.apply_symm_apply]

/-- Relabelling expands any element in the common chart range by exponent renaming. -/
@[simp]
theorem laurentExpansion_reindex (c : LaurentChart R K F) (e : K ≃ K')
    (y : (c.reindex e).range) :
    (c.reindex e).laurentExpansion y = LaurentRing.rename e
      (c.laurentExpansion ⟨y, c.range_reindex e ▸ y.property⟩) := by
  apply (c.reindex e).injective
  rw [toAlgHom_apply, toAlgHom_apply, apply_laurentExpansion, reindex_apply,
    LaurentRing.rename_rename]
  rw [e.symm_comp_self, LaurentRing.rename_id, AlgHom.id_apply, apply_laurentExpansion]

/-- Coefficient data of any reindexed range element follows its renamed expansion. -/
@[simp]
theorem coeff_reindex (c : LaurentChart R K F) (e : K ≃ K')
    (y : (c.reindex e).range) :
    (c.reindex e).coeff y = Finsupp.equivMapDomain (Finsupp.equivCongrLeft e)
      (c.coeff ⟨y, c.range_reindex e ▸ y.property⟩) := by
  rw [coeff_def, laurentExpansion_reindex, LaurentRing.rename_apply,
    AddMonoidAlgebra.coeff_mapDomain, Finsupp.equivMapDomain_eq_mapDomain, coeff_def]
  congr 1
  funext m
  simp [Finsupp.equivCongrLeft_apply, Finsupp.equivMapDomain_eq_mapDomain]

/-- Inverse expansion after relabelling evaluates the inversely renamed Laurent polynomial. -/
@[simp]
theorem laurentExpansion_reindex_symm (c : LaurentChart R K F) (e : K ≃ K')
    (p : LaurentRing R K') :
    (c.reindex e).laurentExpansion.symm p =
      ⟨(c.laurentExpansion.symm (LaurentRing.rename e.symm p) : F),
        (c.range_reindex e).symm ▸
          (c.laurentExpansion.symm (LaurentRing.rename e.symm p)).property⟩ := by
  apply Subtype.ext
  simp only [coe_laurentExpansion_symm_apply, reindex_apply]

/-- Inverse coefficient reconstruction cancels relabelling of the exponent family. -/
@[simp]
theorem coeff_reindex_symm_equivMapDomain (c : LaurentChart R K F) (e : K ≃ K')
    (g : (K →₀ ℤ) →₀ R) :
    (c.reindex e).coeff.symm (Finsupp.equivMapDomain (Finsupp.equivCongrLeft e) g) =
      ⟨(c.coeff.symm g : F),
        (c.range_reindex e).symm ▸ (c.coeff.symm g).property⟩ := by
  apply (c.reindex e).coeff.injective
  rw [LinearEquiv.apply_symm_apply, coeff_reindex, LinearEquiv.apply_symm_apply]

/-- Expand an inverse coordinate after its reindexing formula has been simplified. -/
@[simp↓]
theorem laurentExpansion_reindex_inv_coordinateUnit (c : LaurentChart R K F) (e : K ≃ K')
    (i : K') (h : (((c.coordinateUnit (e.symm i))⁻¹ : Fˣ) : F) ∈ (c.reindex e).range) :
    (c.reindex e).laurentExpansion ⟨(((c.coordinateUnit (e.symm i))⁻¹ : Fˣ) : F), h⟩ =
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 := by
  simpa only [coordinateUnit_reindex] using (c.reindex e).laurentExpansion_inv_coordinateUnit i
    (by simpa only [coordinateUnit_reindex] using h)

/-- An inverse reindexed coordinate has its negative standard-basis coefficient. -/
@[simp↓]
theorem coeff_reindex_inv_coordinateUnit (c : LaurentChart R K F) (e : K ≃ K')
    (i : K') (h : (((c.coordinateUnit (e.symm i))⁻¹ : Fˣ) : F) ∈ (c.reindex e).range) :
    (c.reindex e).coeff ⟨(((c.coordinateUnit (e.symm i))⁻¹ : Fˣ) : F), h⟩ =
      Finsupp.single (-Finsupp.single i 1) 1 := by
  rw [coeff_def, laurentExpansion_reindex_inv_coordinateUnit, AddMonoidAlgebra.coeff_single]

end Semiring


end LaurentChart

end TauCeti

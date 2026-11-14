/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.FreeAbelianCharacter
public import TauCeti.Algebra.MonoidAlgebra.Units
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Multivariable Laurent polynomial rings

For a semiring `R` and a type `K` of variables, the ring of Laurent polynomials
`R[X_i^{±1} : i ∈ K]` is the group algebra of the free abelian group on `K`. This file names it
`TauCeti.LaurentRing R K`, an abbreviation for `AddMonoidAlgebra R (K →₀ ℤ)`, so that everything
known about group algebras applies as it stands: the coefficients `AddMonoidAlgebra.coeff` and
their support, the monomial basis `AddMonoidAlgebra.basis`, and the coefficient maps
`AddMonoidAlgebra.mapRingHom`, which are injective along injective maps by
`AddMonoidAlgebra.map_injective` and localize along with the coefficients by
`AddMonoidAlgebra.isLocalization_coefficients`. The Laurent ring of a domain is a domain,
because `K →₀ ℤ` has unique sums.

What the group algebra does not provide is the description in terms of the variables. The file
supplies it: the variables `X i` are units, an algebra map out of the Laurent ring is determined
by its values on them, and for a commutative `R`-algebra `A` every family of units of `A` is the
family of values of exactly one algebra map. So `LaurentRing R K` is the free commutative
`R`-algebra on a family of invertible generators indexed by `K`. Laurent rings are the coordinate
rings of split tori; in the theory of cluster algebras each cluster is a family of units of the
ambient field, and the Laurent ring is the source of the chart it defines.

The same ring in multiplicative notation, `MonoidAlgebra R (Multiplicative (K →₀ ℤ))`, is the
Hopf algebra of the split torus, whose points `TauCeti.SplitTorus.pointsMulEquiv` computes as a
group. The additive presentation used here is the one of `MvPolynomial` and
`LaurentPolynomial`, so that polynomials and Laurent polynomials share their exponents;
`TauCeti.LaurentRing.aeval` is built from the same universal property
`TauCeti.freeAbelianCharEquiv` of the exponent group.

## Main definitions

* `TauCeti.LaurentRing`: the ring of Laurent polynomials in the variables `K`.
* `TauCeti.LaurentRing.X` and `TauCeti.LaurentRing.unitX`: the variables, as elements and as
  units.
* `TauCeti.LaurentRing.aeval`: the algebra map sending the variables to a given family of units
  of a commutative algebra.
* `TauCeti.LaurentRing.aevalEquiv`: families of units of `A` are the same as `R`-algebra maps
  `LaurentRing R K →ₐ[R] A`.
* `TauCeti.LaurentRing.rename` and `TauCeti.LaurentRing.renameEquiv`: renaming the variables
  along a map, respectively reindexing them along an equivalence.

## Main results

* `TauCeti.LaurentRing.single_eq_smul_prod`: a monomial is its coefficient times the product of
  the integer powers of the variables prescribed by its exponent.
* `TauCeti.LaurentRing.algHom_ext`: algebra maps out of a Laurent ring agree as soon as they
  agree on the variables. The target need not be commutative.
* `TauCeti.LaurentRing.aeval_unique`: `aeval x` is the only algebra map with values `x` on the
  variables.
* `TauCeti.LaurentRing.aeval_rename`: evaluation after renaming is evaluation at the pulled back
  family.
* `TauCeti.LaurentRing.mapRingHom_rename`: coefficient maps commute with renaming.

## Implementation notes

The interface follows the one-variable `LaurentPolynomial` of Mathlib and its evaluation
`TauCeti.laurentEval` and `TauCeti.laurentEvalEquiv` at a unit; `rename` and `renameEquiv` follow
`MvPolynomial.rename` and `MvPolynomial.renameEquiv`.

## References

* S. Fomin and A. Zelevinsky, *Cluster algebras I: Foundations*, J. Amer. Math. Soc. 15 (2002),
  §3, for Laurent polynomials in the variables of a cluster.
* W. Fulton, *Introduction to Toric Varieties*, §1.3, for the group algebra of a lattice as the
  coordinate ring of a torus.
-/

public section

open AddMonoidAlgebra

namespace TauCeti

/-- The ring of Laurent polynomials in the variables `K` with coefficients in `R`: the group
algebra of the free abelian group `K →₀ ℤ` of exponents. A Laurent polynomial is a finite formal
`R`-linear combination of the monomials `AddMonoidAlgebra.single m 1`, one for each exponent
`m : K →₀ ℤ`. -/
abbrev LaurentRing (R : Type*) [Semiring R] (K : Type*) : Type _ :=
  AddMonoidAlgebra R (K →₀ ℤ)

namespace LaurentRing

variable {R : Type*} {K K' K'' : Type*}

section Semiring

variable [Semiring R]

/-- The variable of the Laurent ring indexed by `i`: the monomial whose exponent is the `i`-th
standard basis vector. -/
noncomputable def X (i : K) : LaurentRing R K :=
  single (Finsupp.single i 1) 1

theorem X_def (i : K) : (X i : LaurentRing R K) = single (Finsupp.single i 1) 1 :=
  (rfl)

/-- The coefficient family of a Laurent variable is its standard-basis singleton. -/
@[simp]
theorem coeff_X (i : K) : (X i : LaurentRing R K).coeff =
    Finsupp.single (Finsupp.single i 1) 1 := by
  rw [X_def, coeff_single]

/-- The variable of the Laurent ring indexed by `i`, as a unit. Its inverse is the monomial
whose exponent is the negative of the `i`-th standard basis vector. -/
noncomputable def unitX (i : K) : (LaurentRing R K)ˣ :=
  unitsSingle (1, Multiplicative.ofAdd (toAddUnits (Finsupp.single i 1)))

@[simp]
theorem val_unitX (i : K) : ((unitX i : (LaurentRing R K)ˣ) : LaurentRing R K) = X i := by
  simp [unitX, X_def]

theorem isUnit_X (i : K) : IsUnit (X i : LaurentRing R K) :=
  ⟨unitX i, val_unitX i⟩

/-- The integer powers of a variable are the monomials supported on its coordinate axis. -/
@[simp]
theorem val_unitX_zpow (i : K) (n : ℤ) :
    ((unitX i ^ n : (LaurentRing R K)ˣ) : LaurentRing R K) = single (Finsupp.single i n) 1 := by
  simp [unitX, ← map_zpow, ← ofAdd_zsmul]

@[simp]
theorem val_inv_unitX (i : K) :
    (((unitX i)⁻¹ : (LaurentRing R K)ˣ) : LaurentRing R K) = single (Finsupp.single i (-1)) 1 := by
  simpa using val_unitX_zpow (R := R) i (-1)

theorem X_pow (i : K) (n : ℕ) :
    (X i : LaurentRing R K) ^ n = single (Finsupp.single i (n : ℤ)) 1 := by
  simpa using val_unitX_zpow (R := R) i n

/-- Coefficient maps fix the variables. -/
@[simp]
theorem mapRingHom_X {S : Type*} [Semiring S] (φ : R →+* S) (i : K) :
    mapRingHom (K →₀ ℤ) φ (X i) = X i := by
  simp [X_def]

end Semiring

section CommSemiring

variable [CommSemiring R]

/-- A monomial of the Laurent ring is its coefficient times the product of the integer powers of
the variables prescribed by its exponent. -/
theorem single_eq_smul_prod (m : K →₀ ℤ) (r : R) :
    (single m r : LaurentRing R K) =
      r • ((m.prod fun i n ↦ unitX i ^ n : (LaurentRing R K)ˣ) : LaurentRing R K) := by
  have h : (m.prod fun i n ↦ unitX i ^ n : (LaurentRing R K)ˣ) =
      (of R (K →₀ ℤ)).toHomUnits (Multiplicative.ofAdd m) := by
    rw [← freeAbelianCharEquiv_symm_apply_ofAdd]
    congr 1
    refine (MulEquiv.symm_apply_eq _).2 (funext fun i ↦ Units.ext ?_)
    simp [X_def]
  simp [h, smul_single]

section Semiring

variable {A : Type*} [Semiring A] [Algebra R A]

/-- Algebra maps out of a Laurent ring agree as soon as they agree on the variables. The target
is an arbitrary `R`-algebra, not necessarily commutative. -/
@[ext high + 1]
theorem algHom_ext ⦃f g : LaurentRing R K →ₐ[R] A⦄ (h : ∀ i, f (X i) = g (X i)) : f = g := by
  refine AddMonoidAlgebra.algHom_ext (fun m ↦ ?_) (Subsingleton.elim _ _)
  induction m using Finsupp.induction_linear with
  | zero => simp [← one_def]
  | add a b ha hb =>
    rw [← mul_one (1 : R), ← single_mul_single, map_mul, map_mul, ha, hb]
  | single i n =>
    -- Both maps send the unit `unitX i` to the same unit of `A`, hence agree on its powers.
    have hu : Units.map (f : LaurentRing R K →* A) (unitX i) =
        Units.map (g : LaurentRing R K →* A) (unitX i) := Units.ext (by simpa using h i)
    simpa [← map_zpow] using congr(((($hu) ^ n : Aˣ) : A))

end Semiring

section Aeval

variable {A B : Type*} [CommSemiring A] [Algebra R A] [CommSemiring B] [Algebra R B]

/-- Evaluation of a Laurent polynomial at a family of units of a commutative `R`-algebra: the
`R`-algebra map sending the variable `X i` to `x i`, and hence `X i ^ n` to `x i ^ n` for every
integer `n`. -/
noncomputable def aeval (x : K → Aˣ) : LaurentRing R K →ₐ[R] A :=
  AddMonoidAlgebra.lift R A (K →₀ ℤ) ((Units.coeHom A).comp (freeAbelianCharEquiv.symm x))

/-- Evaluation sends a monomial to its coefficient times the corresponding product of integer
powers of the chosen units. -/
@[simp]
theorem aeval_single (x : K → Aˣ) (m : K →₀ ℤ) (r : R) :
    aeval x (single m r) = r • ((m.prod fun i n ↦ x i ^ n : Aˣ) : A) := by
  simp [aeval]

@[simp]
theorem aeval_X (x : K → Aˣ) (i : K) : aeval x (X i : LaurentRing R K) = x i := by
  simp [X_def]

/-- The unit of `A` obtained from the variable `X i` under evaluation at `x` is `x i`. -/
@[simp]
theorem map_aeval_unitX (x : K → Aˣ) (i : K) :
    Units.map (aeval (R := R) x : LaurentRing R K →* A) (unitX i) = x i :=
  Units.ext (by simp)

/-- Evaluation at `x` is the only algebra map with values `x` on the variables. -/
theorem aeval_unique (f : LaurentRing R K →ₐ[R] A) (x : K → Aˣ) (h : ∀ i, f (X i) = x i) :
    f = aeval x :=
  algHom_ext fun i ↦ by rw [h, aeval_X]

/-- Evaluating at the variables themselves is the identity. -/
@[simp]
theorem aeval_unitX_left :
    aeval (unitX : K → (LaurentRing R K)ˣ) = AlgHom.id R (LaurentRing R K) :=
  (aeval_unique _ _ fun i ↦ by simp).symm

/-- Evaluation is natural in the target algebra. -/
theorem comp_aeval (φ : A →ₐ[R] B) (x : K → Aˣ) :
    φ.comp (aeval x) = aeval fun i ↦ Units.map (φ : A →* B) (x i) :=
  aeval_unique _ _ fun i ↦ by simp

/-- **The Laurent ring is the free commutative `R`-algebra on a family of invertible
generators**: its `R`-algebra maps to a commutative `R`-algebra `A` are exactly the families of
units of `A`, through evaluation of the variables. -/
noncomputable def aevalEquiv : (K → Aˣ) ≃ (LaurentRing R K →ₐ[R] A) where
  toFun := aeval
  invFun f i := Units.map (f : LaurentRing R K →* A) (unitX i)
  left_inv x := funext fun i ↦ map_aeval_unitX x i
  right_inv f := (aeval_unique f _ fun i ↦ by simp).symm

@[simp]
theorem aevalEquiv_apply (x : K → Aˣ) : aevalEquiv (R := R) x = aeval x :=
  (rfl)

theorem aevalEquiv_symm_apply (f : LaurentRing R K →ₐ[R] A) (i : K) :
    aevalEquiv.symm f i = Units.map (f : LaurentRing R K →* A) (unitX i) :=
  (rfl)

/-- The family of units represented by an algebra map consists of its values on the
variables. -/
@[simp]
theorem val_aevalEquiv_symm_apply (f : LaurentRing R K →ₐ[R] A) (i : K) :
    ((aevalEquiv.symm f i : Aˣ) : A) = f (X i) := by
  simp [aevalEquiv_symm_apply]

/-- Reading the family of units from its evaluation map recovers that family. -/
@[simp]
theorem aevalEquiv_symm_aeval (x : K → Aˣ) : aevalEquiv.symm (aeval (R := R) x) = x :=
  (aevalEquiv (R := R)).symm_apply_apply x

/-- Evaluating at the family of units represented by an algebra map recovers that map. -/
@[simp]
theorem aeval_aevalEquiv_symm (f : LaurentRing R K →ₐ[R] A) : aeval (aevalEquiv.symm f) = f :=
  (aevalEquiv (R := R)).apply_symm_apply f

end Aeval

section Rename

/-- Rename the variables of a Laurent polynomial along a map of index types. -/
noncomputable def rename (f : K → K') : LaurentRing R K →ₐ[R] LaurentRing R K' :=
  mapDomainAlgHom R R (Finsupp.mapDomain.addMonoidHom f)

/-- Renaming the variables pushes the coefficients forward along the induced map of
exponents. -/
theorem rename_apply (f : K → K') (p : LaurentRing R K) :
    rename f p = mapDomain (Finsupp.mapDomain f) p :=
  (rfl)

@[simp]
theorem rename_single (f : K → K') (m : K →₀ ℤ) (r : R) :
    rename f (single m r) = single (m.mapDomain f) r := by
  simp [rename_apply]

@[simp]
theorem rename_X (f : K → K') (i : K) : rename f (X i : LaurentRing R K) = X (f i) := by
  simp [X_def]

@[simp]
theorem map_rename_unitX (f : K → K') (i : K) :
    Units.map (rename (R := R) f : LaurentRing R K →* LaurentRing R K') (unitX i) =
      unitX (f i) :=
  Units.ext (by simp)

@[simp]
theorem rename_id : rename id = AlgHom.id R (LaurentRing R K) :=
  algHom_ext fun i ↦ by simp

theorem rename_comp_rename (f : K → K') (g : K' → K'') :
    (rename (R := R) g).comp (rename f) = rename (g ∘ f) :=
  algHom_ext fun i ↦ by simp

@[simp]
theorem rename_rename (f : K → K') (g : K' → K'') (p : LaurentRing R K) :
    rename g (rename f p) = rename (g ∘ f) p :=
  DFunLike.congr_fun (rename_comp_rename f g) p

/-- Renaming the variables along an injective map is injective. -/
theorem rename_injective {f : K → K'} (hf : Function.Injective f) :
    Function.Injective (rename f : LaurentRing R K → LaurentRing R K') := fun p q h ↦
  mapDomain_injective (Finsupp.mapDomain_injective hf) (by rwa [rename_apply, rename_apply] at h)

theorem aeval_comp_rename {A : Type*} [CommSemiring A] [Algebra R A] (f : K → K')
    (x : K' → Aˣ) : (aeval (R := R) x).comp (rename f) = aeval (x ∘ f) :=
  aeval_unique _ _ fun i ↦ by simp

/-- Evaluation after renaming the variables is evaluation at the pulled back family of units. -/
@[simp]
theorem aeval_rename {A : Type*} [CommSemiring A] [Algebra R A] (f : K → K') (x : K' → Aˣ)
    (p : LaurentRing R K) : aeval x (rename f p) = aeval (x ∘ f) p :=
  DFunLike.congr_fun (aeval_comp_rename f x) p

/-- Coefficient maps commute with renaming the variables. -/
theorem mapRingHom_rename {S : Type*} [CommSemiring S] (φ : R →+* S) (f : K → K')
    (p : LaurentRing R K) :
    mapRingHom (K' →₀ ℤ) φ (rename f p) = rename f (mapRingHom (K →₀ ℤ) φ p) := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single m r => simp

variable (R) in
/-- Reindex the variables of a Laurent ring along an equivalence of index types. -/
noncomputable def renameEquiv (e : K ≃ K') : LaurentRing R K ≃ₐ[R] LaurentRing R K' :=
  AddMonoidAlgebra.domCongr R R (Finsupp.domCongr e : (K →₀ ℤ) ≃+ (K' →₀ ℤ))

@[simp]
theorem renameEquiv_apply (e : K ≃ K') (p : LaurentRing R K) :
    renameEquiv R e p = rename e p := by
  induction p using induction_linear with
  | zero => simp
  | add p q hp hq => simp [hp, hq]
  | single m r =>
    simp [renameEquiv, AddMonoidAlgebra.domCongr_single, Finsupp.equivMapDomain_eq_mapDomain]

@[simp]
theorem renameEquiv_refl : renameEquiv R (Equiv.refl K) = AlgEquiv.refl := by
  simp [renameEquiv]

@[simp]
theorem renameEquiv_symm (e : K ≃ K') : (renameEquiv R e).symm = renameEquiv R e.symm := by
  simp [renameEquiv]

@[simp]
theorem renameEquiv_trans (e : K ≃ K') (e' : K' ≃ K'') :
    (renameEquiv R e).trans (renameEquiv R e') = renameEquiv R (e.trans e') := by
  simp [renameEquiv]

end Rename

end CommSemiring

/-! ### Checks -/

/-- The Laurent ring of a domain is a domain. -/
example [CommRing R] [IsDomain R] : IsDomain (LaurentRing R K) := inferInstance

/-- With no variables, the Laurent ring is the coefficient ring. -/
noncomputable example [CommSemiring R] [IsEmpty K] : LaurentRing R K ≃ₐ[R] R :=
  uniqueAlgEquiv R (K →₀ ℤ)

/-- Evaluation at `X = 1` is an algebra map over `ℤ` whose kernel contains `X - 1`. -/
example : aeval (fun _ : Unit ↦ (1 : ℤˣ)) (X () - 1 : LaurentRing ℤ Unit) = 0 := by simp

/-- No algebra map to `ℤ` sends `X` to `2`: it would also send the inverse of `X` to an inverse
of `2`. -/
example (f : LaurentRing ℤ Unit →ₐ[ℤ] ℤ) : f (X ()) ≠ 2 := fun h ↦ by
  have h2 : IsUnit (2 : ℤ) := h ▸ (isUnit_X ()).map f
  exact absurd (Int.isUnit_iff.1 h2) (by decide)

end LaurentRing

end TauCeti

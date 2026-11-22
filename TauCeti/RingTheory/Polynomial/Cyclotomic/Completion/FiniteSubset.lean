/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Polynomial.Cyclotomic.Completion.Map

/-!
# The cyclotomic completion as a limit over finite sets of orders

Every index of the cyclotomic completion `R[q]^S` is a finite product of cyclotomic polynomials,
so it only involves finitely many orders of `S`. Consequently `R[q]^S` is the inverse limit of the
completions `R[q]^U` over the finite subsets `U` of `S`, along the order restrictions
`R[q]^V → R[q]^U` for `U ⊆ V`.

Here this limit is the subalgebra `TauCeti.CycloCompletion.finiteSubsetCompatSubalgebra R S` of
compatible families in `∏_U R[q]^U`, `U` running over the finite subsets of `S`, with the topology
induced from the product. The comparison `TauCeti.CycloCompletion.finiteSubsetEquiv` sends an
element to its family of restrictions; its inverse reads the residue modulo an index `f` off the
coordinate at any finite `U ⊆ S` with `f ∈ cycloIndex R U`, a common finite superset showing that
the choice of `U` does not matter. The comparison is a homeomorphism and commutes with order
restriction and coefficient change. No hypothesis on `R` is needed.

This reduces statements about arbitrary order sets to finite ones: for instance two elements of
`R[q]^S` are equal once all their restrictions to finite subsets of `S` are
(`TauCeti.CycloCompletion.ext_restrict`), and an element of `R[q]^S` can be built from compatible
elements of the completions at finite order sets.

## Main definitions

* `TauCeti.CycloCompletion.finiteSubsetCompatSubalgebra R S`: the compatible families of the
  finite-subset system.
* `TauCeti.CycloCompletion.FiniteSubsetLimit R S`: the finite-subset limit, with its coordinates
  `FiniteSubsetLimit.proj U`, order restriction `FiniteSubsetLimit.restrict` and coefficient change
  `FiniteSubsetLimit.map`.
* `TauCeti.CycloCompletion.finiteSubsetEquiv`: the comparison
  `R[q]^S ≃A[R] FiniteSubsetLimit R S`.

## Main results

* `TauCeti.CycloCompletion.FiniteSubsetLimit.restrict_proj`: the transition equation.
* `TauCeti.CycloCompletion.FiniteSubsetLimit.proj_proj_eq`: the residue modulo an index does not
  depend on the finite subset it is read from.
* `TauCeti.CycloCompletion.proj_finiteSubsetEquiv`,
  `TauCeti.CycloCompletion.proj_finiteSubsetEquiv_symm`: the coordinates of the comparison and the
  reconstruction equation of its inverse.
* `TauCeti.CycloCompletion.finiteSubsetEquiv_restrict`,
  `TauCeti.CycloCompletion.finiteSubsetEquiv_map`: naturality in the order set and in the
  coefficient ring.
* `TauCeti.CycloCompletion.ext_restrict`: extensionality by restrictions to finite subsets.

## References

* K. Habiro, *Cyclotomic completions of polynomial rings*, Publ. Res. Inst. Math. Sci. **40**
  (2004), 1127–1146, §3.1.
-/

public section

open Polynomial

namespace TauCeti

namespace CycloCompletion

section Limit

variable (R : Type*) [CommRing R] (S : Set ℕ)

/-- The compatible families in `∏_U R[q]^U`, `U` running over the finite subsets of `S`: those `x`
with `restrict (x V) = x U` whenever `U ⊆ V`. -/
noncomputable def finiteSubsetCompatSubalgebra :
    Subalgebra R (∀ U : {U : Set ℕ // U ⊆ S ∧ U.Finite}, CycloCompletion R U.val) where
  carrier := {x | ∀ (U V : {U : Set ℕ // U ⊆ S ∧ U.Finite}) (h : U.val ⊆ V.val),
    restrict R h (x V) = x U}
  mul_mem' hx hy U V h := by simp only [Pi.mul_apply, map_mul, hx U V h, hy U V h]
  add_mem' hx hy U V h := by simp only [Pi.add_apply, map_add, hx U V h, hy U V h]
  algebraMap_mem' r U V h := (restrict R h).commutes r

variable {R S} in
theorem mem_finiteSubsetCompatSubalgebra
    {x : ∀ U : {U : Set ℕ // U ⊆ S ∧ U.Finite}, CycloCompletion R U.val} :
    x ∈ finiteSubsetCompatSubalgebra R S ↔ ∀ (U V : {U : Set ℕ // U ⊆ S ∧ U.Finite})
      (h : U.val ⊆ V.val), restrict R h (x V) = x U := by
  rw [finiteSubsetCompatSubalgebra]
  rfl

/-- The finite-subset limit `lim_U R[q]^U` over the finite subsets `U` of `S`, realised as the
algebra of compatible families, with the topology induced from the product. -/
abbrev FiniteSubsetLimit := ↥(finiteSubsetCompatSubalgebra R S)

namespace FiniteSubsetLimit

variable {R S}

/-- The coordinate `lim_U R[q]^U → R[q]^U` at a finite subset `U` of `S`. -/
noncomputable def proj (U : {U : Set ℕ // U ⊆ S ∧ U.Finite}) :
    FiniteSubsetLimit R S →ₐ[R] CycloCompletion R U.val :=
  (Pi.evalAlgHom R (fun U : {U : Set ℕ // U ⊆ S ∧ U.Finite} ↦ CycloCompletion R U.val) U).comp
    (finiteSubsetCompatSubalgebra R S).val

theorem proj_apply (U : {U : Set ℕ // U ⊆ S ∧ U.Finite}) (y : FiniteSubsetLimit R S) :
    proj U y = (y : ∀ U : {U : Set ℕ // U ⊆ S ∧ U.Finite}, CycloCompletion R U.val) U := by
  simp [proj]

@[simp]
theorem proj_mk (U : {U : Set ℕ // U ⊆ S ∧ U.Finite})
    (x : ∀ U : {U : Set ℕ // U ⊆ S ∧ U.Finite}, CycloCompletion R U.val)
    (hx : x ∈ finiteSubsetCompatSubalgebra R S) : proj U ⟨x, hx⟩ = x U :=
  proj_apply U ⟨x, hx⟩

/-- The transition equation: for `U ⊆ V`, restricting the coordinate at `V` to `U` gives the
coordinate at `U`. -/
@[simp]
theorem restrict_proj {U V : {U : Set ℕ // U ⊆ S ∧ U.Finite}} (h : U.val ⊆ V.val)
    (y : FiniteSubsetLimit R S) : restrict R h (proj V y) = proj U y := by
  rw [proj_apply, proj_apply]
  exact mem_finiteSubsetCompatSubalgebra.mp y.property U V h

/-- An element of the finite-subset limit is determined by its coordinates. -/
@[ext]
theorem ext {y z : FiniteSubsetLimit R S} (h : ∀ U, proj U y = proj U z) : y = z := by
  refine Subtype.ext (funext fun U ↦ ?_)
  rw [← proj_apply, ← proj_apply, h]

/-- The residue of an element modulo an index `f` does not depend on the finite subset `U` with
`f ∈ cycloIndex R U` from whose coordinate it is read. -/
theorem proj_proj_eq {U V : {U : Set ℕ // U ⊆ S ∧ U.Finite}} {f : R[X]}
    (hU : f ∈ cycloIndex R U.val) (hV : f ∈ cycloIndex R V.val) (y : FiniteSubsetLimit R S) :
    CycloCompletion.proj ⟨f, hU⟩ (proj U y) = CycloCompletion.proj ⟨f, hV⟩ (proj V y) := by
  obtain ⟨W, hUW, hVW⟩ : ∃ W : {U : Set ℕ // U ⊆ S ∧ U.Finite}, U.val ⊆ W.val ∧ V.val ⊆ W.val :=
    ⟨⟨_, Set.union_subset U.property.left V.property.left,
      U.property.right.union V.property.right⟩, Set.subset_union_left, Set.subset_union_right⟩
  rw [← restrict_proj hUW, ← restrict_proj hVW, proj_restrict, proj_restrict]
  -- Both sides are the coordinate of `proj W y` at the polynomial `f`; `Submonoid.inclusion` does
  -- not change the underlying polynomial, and the two sides only typecheck up to this identity.
  rfl

variable (R S) in
/-- A map into the finite-subset limit is continuous exactly when all its coordinates are. -/
theorem continuous_iff {X : Type*} [TopologicalSpace X] {g : X → FiniteSubsetLimit R S} :
    Continuous g ↔ ∀ U, Continuous (proj U ∘ g) := by
  simp only [continuous_induced_rng, continuous_pi_iff, Function.comp_def, proj_apply]

@[fun_prop, continuity]
theorem continuous_proj (U : {U : Set ℕ // U ⊆ S ∧ U.Finite}) : Continuous (proj U (R := R)) :=
  (continuous_iff R S).mp continuous_id U

end FiniteSubsetLimit

end Limit

section Equiv

variable {R : Type*} [CommRing R] {S : Set ℕ}

/-- The restrictions of an element of `R[q]^S` to the finite subsets of `S`. -/
private noncomputable def toFiniteSubsetLimit : CycloCompletion R S →ₐ[R] FiniteSubsetLimit R S :=
  (AlgHom.pi fun U : {U : Set ℕ // U ⊆ S ∧ U.Finite} ↦ restrict R U.property.left).codRestrict _
    fun x ↦ mem_finiteSubsetCompatSubalgebra.mpr fun U V h ↦ by simp

private theorem proj_toFiniteSubsetLimit (U : {U : Set ℕ // U ⊆ S ∧ U.Finite})
    (x : CycloCompletion R S) :
    FiniteSubsetLimit.proj U (toFiniteSubsetLimit x) = restrict R U.property.left x := by
  simp [FiniteSubsetLimit.proj_apply, toFiniteSubsetLimit]

/-- A finite subset of `S` over which the index `f` is defined. -/
private noncomputable def finiteSubsetOf (f : cycloIndex R S) : {U : Set ℕ // U ⊆ S ∧ U.Finite} :=
  ⟨_, (exists_finite_subset_mem_cycloIndex f.property).choose_spec.left,
    (exists_finite_subset_mem_cycloIndex f.property).choose_spec.right.left⟩

private theorem mem_cycloIndex_finiteSubsetOf (f : cycloIndex R S) :
    (f : R[X]) ∈ cycloIndex R (finiteSubsetOf f).val :=
  (exists_finite_subset_mem_cycloIndex f.property).choose_spec.right.right

/-- The residue modulo `f`, read off a finite subset over which `f` is defined. -/
private noncomputable def projFiniteSubsetOf (f : cycloIndex R S) :
    FiniteSubsetLimit R S →ₐ[R] AdjoinRoot (f : R[X]) :=
  (proj (⟨f, mem_cycloIndex_finiteSubsetOf f⟩ : cycloIndex R (finiteSubsetOf f).val)).comp
    (FiniteSubsetLimit.proj (finiteSubsetOf f))

/-- The element of `R[q]^S` whose residue modulo `f` is read off a finite subset over which `f` is
defined. -/
private noncomputable def ofFiniteSubsetLimit : FiniteSubsetLimit R S →ₐ[R] CycloCompletion R S :=
  liftCompatAlgHom projFiniteSubsetOf fun f g h ↦ AlgHom.ext fun y ↦ by
    -- Read both residues off the union of the two chosen finite subsets.
    obtain ⟨W, hfW, hgW⟩ : ∃ W : {U : Set ℕ // U ⊆ S ∧ U.Finite},
        (f : R[X]) ∈ cycloIndex R W.val ∧ (g : R[X]) ∈ cycloIndex R W.val :=
      ⟨⟨(finiteSubsetOf f).val ∪ (finiteSubsetOf g).val,
        Set.union_subset (finiteSubsetOf f).property.left (finiteSubsetOf g).property.left,
        (finiteSubsetOf f).property.right.union (finiteSubsetOf g).property.right⟩,
        cycloIndex_mono Set.subset_union_left (mem_cycloIndex_finiteSubsetOf f),
        cycloIndex_mono Set.subset_union_right (mem_cycloIndex_finiteSubsetOf g)⟩
    rw [AlgHom.comp_apply, projFiniteSubsetOf, projFiniteSubsetOf, AlgHom.comp_apply,
      AlgHom.comp_apply, FiniteSubsetLimit.proj_proj_eq (mem_cycloIndex_finiteSubsetOf g) hgW y,
      FiniteSubsetLimit.proj_proj_eq (mem_cycloIndex_finiteSubsetOf f) hfW y]
    exact algHomOfDvd_proj (S := W.val) (f := ⟨(f : R[X]), hfW⟩) (g := ⟨(g : R[X]), hgW⟩) h _

private theorem proj_ofFiniteSubsetLimit (f : cycloIndex R S) {U : {U : Set ℕ // U ⊆ S ∧ U.Finite}}
    (hf : (f : R[X]) ∈ cycloIndex R U.val) (y : FiniteSubsetLimit R S) :
    proj f (ofFiniteSubsetLimit y) = proj ⟨f, hf⟩ (FiniteSubsetLimit.proj U y) := by
  rw [ofFiniteSubsetLimit, proj_liftCompatAlgHom, projFiniteSubsetOf, AlgHom.comp_apply]
  exact FiniteSubsetLimit.proj_proj_eq _ hf y

variable (R S) in
/-- The comparison `R[q]^S ≃ lim_U R[q]^U` of the cyclotomic completion with the limit over the
finite subsets `U` of `S`: an element goes to its family of restrictions. -/
noncomputable def finiteSubsetEquiv : CycloCompletion R S ≃A[R] FiniteSubsetLimit R S where
  toAlgEquiv := AlgEquiv.ofAlgHom toFiniteSubsetLimit ofFiniteSubsetLimit
    (AlgHom.ext fun y ↦ FiniteSubsetLimit.ext fun U ↦ ext fun f ↦ by
      rw [AlgHom.comp_apply, proj_toFiniteSubsetLimit, proj_restrict, proj_ofFiniteSubsetLimit]
      -- `Submonoid.inclusion` does not change the underlying polynomial of the index.
      rfl)
    (AlgHom.ext fun x ↦ ext fun f ↦ by
      rw [AlgHom.comp_apply, proj_ofFiniteSubsetLimit f (mem_cycloIndex_finiteSubsetOf f),
        proj_toFiniteSubsetLimit, proj_restrict]
      -- `Submonoid.inclusion` does not change the underlying polynomial of the index.
      rfl)
  continuous_toFun := (FiniteSubsetLimit.continuous_iff R S).mpr fun U ↦ by
    convert CycloCompletion.continuous_restrict (R := R) U.property.left using 1
    exact funext (proj_toFiniteSubsetLimit U)
  continuous_invFun := continuous_iff.mpr fun f ↦ by
    convert (isLocallyConstant_proj ⟨(f : R[X]), mem_cycloIndex_finiteSubsetOf f⟩).comp_continuous
      (FiniteSubsetLimit.continuous_proj (finiteSubsetOf f)) using 1
    exact funext (proj_ofFiniteSubsetLimit f _)

/-- The coordinate of the comparison at a finite subset `U` of `S` is the restriction to `U`. -/
@[simp]
theorem proj_finiteSubsetEquiv (U : {U : Set ℕ // U ⊆ S ∧ U.Finite}) (x : CycloCompletion R S) :
    FiniteSubsetLimit.proj U (finiteSubsetEquiv R S x) = restrict R U.property.left x :=
  proj_toFiniteSubsetLimit U x

/-- The reconstruction equation: the residue modulo an index `f` of the element of `R[q]^S`
corresponding to a compatible family is the residue of its coordinate at any finite subset `U` of
`S` with `f ∈ cycloIndex R U`. -/
theorem proj_finiteSubsetEquiv_symm (f : cycloIndex R S) {U : {U : Set ℕ // U ⊆ S ∧ U.Finite}}
    (hf : (f : R[X]) ∈ cycloIndex R U.val) (y : FiniteSubsetLimit R S) :
    proj f ((finiteSubsetEquiv R S).symm y) = proj ⟨f, hf⟩ (FiniteSubsetLimit.proj U y) :=
  proj_ofFiniteSubsetLimit f hf y

/-- Restricting the element corresponding to a compatible family to a finite subset `U` of `S`
recovers the coordinate at `U`. -/
@[simp]
theorem restrict_finiteSubsetEquiv_symm (U : {U : Set ℕ // U ⊆ S ∧ U.Finite})
    (y : FiniteSubsetLimit R S) :
    restrict R U.property.left ((finiteSubsetEquiv R S).symm y) = FiniteSubsetLimit.proj U y := by
  rw [← proj_finiteSubsetEquiv, ContinuousAlgEquiv.apply_symm_apply]

/-- Elements of `R[q]^S` with the same restrictions to all finite subsets of `S` are equal. -/
theorem ext_restrict {x y : CycloCompletion R S}
    (h : ∀ (U : Set ℕ) (hU : U ⊆ S), U.Finite → restrict R hU x = restrict R hU y) : x = y :=
  EquivLike.injective (finiteSubsetEquiv R S) <| FiniteSubsetLimit.ext fun U ↦ by
    rw [proj_finiteSubsetEquiv, proj_finiteSubsetEquiv, h U.val U.property.left U.property.right]

end Equiv

/-! ### Naturality -/

namespace FiniteSubsetLimit

section Restrict

variable {R : Type*} [CommRing R] {S T : Set ℕ}

variable (R) in
/-- Order restriction `lim_{U ⊆ S} R[q]^U → lim_{U ⊆ T} R[q]^U` for `T ⊆ S`, forgetting the
coordinates at finite subsets of `S` that are not contained in `T`. -/
noncomputable def restrict (hTS : T ⊆ S) : FiniteSubsetLimit R S →ₐ[R] FiniteSubsetLimit R T :=
  (AlgHom.pi fun U : {U : Set ℕ // U ⊆ T ∧ U.Finite} ↦
    proj ⟨U.val, U.property.left.trans hTS, U.property.right⟩).codRestrict _ fun y ↦
    mem_finiteSubsetCompatSubalgebra.mpr fun U V h ↦ by
      simpa only [AlgHom.pi_apply] using
        restrict_proj (U := ⟨U.val, U.property.left.trans hTS, U.property.right⟩)
          (V := ⟨V.val, V.property.left.trans hTS, V.property.right⟩) h y

@[simp]
theorem proj_restrict (hTS : T ⊆ S) (U : {U : Set ℕ // U ⊆ T ∧ U.Finite})
    (y : FiniteSubsetLimit R S) :
    proj U (restrict R hTS y) = proj ⟨U.val, U.property.left.trans hTS, U.property.right⟩ y := by
  simp [proj_apply, restrict]

@[fun_prop, continuity]
theorem continuous_restrict (hTS : T ⊆ S) : Continuous (restrict R hTS) :=
  (continuous_iff R T).mpr fun U ↦ by
    simpa only [Function.comp_def, proj_restrict] using continuous_proj _

end Restrict

section Map

variable {R R' : Type*} [CommRing R] [CommRing R'] {S : Set ℕ}

/-- Coefficient change `lim_U R[q]^U → lim_U R'[q]^U` along `φ : R →+* R'`, coordinatewise. -/
noncomputable def map (φ : R →+* R') : FiniteSubsetLimit R S →+* FiniteSubsetLimit R' S :=
  (RingHom.pi fun U : {U : Set ℕ // U ⊆ S ∧ U.Finite} ↦
    (CycloCompletion.map φ U.val).comp (proj U (R := R)).toRingHom).codRestrict
    (finiteSubsetCompatSubalgebra R' S) fun y ↦
    mem_finiteSubsetCompatSubalgebra.mpr fun U V h ↦ by simp

@[simp]
theorem proj_map (φ : R →+* R') (U : {U : Set ℕ // U ⊆ S ∧ U.Finite})
    (y : FiniteSubsetLimit R S) :
    proj U (map φ y) = CycloCompletion.map φ U.val (proj U y) := by
  simp [proj_apply, map]

@[fun_prop, continuity]
theorem continuous_map (φ : R →+* R') : Continuous (map φ (S := S)) :=
  (continuous_iff R' S).mpr fun U ↦ by
    simpa only [Function.comp_def, proj_map] using
      (CycloCompletion.continuous_map φ U.val).comp (continuous_proj U)

end Map

end FiniteSubsetLimit

section Naturality

variable {R R' : Type*} [CommRing R] [CommRing R'] {S T : Set ℕ}

/-- The comparison commutes with order restriction. -/
theorem finiteSubsetEquiv_restrict (hTS : T ⊆ S) (x : CycloCompletion R S) :
    finiteSubsetEquiv R T (restrict R hTS x) =
      FiniteSubsetLimit.restrict R hTS (finiteSubsetEquiv R S x) :=
  FiniteSubsetLimit.ext fun U ↦ by simp

/-- The comparison commutes with coefficient change. -/
theorem finiteSubsetEquiv_map (φ : R →+* R') (x : CycloCompletion R S) :
    finiteSubsetEquiv R' S (map φ S x) =
      FiniteSubsetLimit.map φ (finiteSubsetEquiv R S x) :=
  FiniteSubsetLimit.ext fun U ↦ by simp

end Naturality

end CycloCompletion

/-! ### Examples -/

open CycloCompletion

/-- With no orders the finite-subset limit is the zero ring. -/
example : Subsingleton (FiniteSubsetLimit ℤ ∅) :=
  (EquivLike.injective (finiteSubsetEquiv ℤ ∅).symm).subsingleton

/-- The comparison sends `q`, `q ^ 2` and `1 - q` to their images on every finite subset. -/
example (S : Set ℕ) (U : {U : Set ℕ // U ⊆ S ∧ U.Finite}) :
    FiniteSubsetLimit.proj U (finiteSubsetEquiv ℤ S (fromPoly ℤ S X)) = fromPoly ℤ U.val X ∧
      FiniteSubsetLimit.proj U (finiteSubsetEquiv ℤ S (fromPoly ℤ S (X ^ 2))) =
        fromPoly ℤ U.val (X ^ 2) ∧
      FiniteSubsetLimit.proj U (finiteSubsetEquiv ℤ S (fromPoly ℤ S (1 - X))) =
        fromPoly ℤ U.val (1 - X) := by
  simp

/-- If an element of `ℤ[q]^{1,2}` restricts to the constant `a` on `{1}` and to `b` on `{2}`, then
some polynomial is congruent to `a` modulo `(q - 1) ^ k` and to `b` modulo `(q + 1) ^ k`. -/
private theorem exists_poly_of_restrict_one_two (z : CycloCompletion ℤ {1, 2}) (a b : ℤ) (k : ℕ)
    (ha : restrict ℤ (by simp : ({1} : Set ℕ) ⊆ {1, 2}) z = algebraMap ℤ _ a)
    (hb : restrict ℤ (by simp : ({2} : Set ℕ) ⊆ {1, 2}) z = algebraMap ℤ _ b) :
    ∃ p : ℤ[X], (X - 1) ^ k ∣ p - C a ∧ (X + 1) ^ k ∣ p - C b := by
  have h1 : cyclotomic 1 ℤ ^ k ∈ cycloIndex ℤ {1} := cyclotomic_pow_mem_cycloIndex rfl k
  have h2 : cyclotomic 2 ℤ ^ k ∈ cycloIndex ℤ {2} := cyclotomic_pow_mem_cycloIndex rfl k
  have h12 : cyclotomic 1 ℤ ^ k * cyclotomic 2 ℤ ^ k ∈ cycloIndex ℤ {1, 2} :=
    mul_mem (cyclotomic_pow_mem_cycloIndex (by simp) k) (cyclotomic_pow_mem_cycloIndex (by simp) k)
  obtain ⟨p, hp⟩ := AdjoinRoot.mk_surjective (proj ⟨_, h12⟩ z)
  have ha' := congrArg (proj ⟨_, h1⟩) ha
  have hb' := congrArg (proj ⟨_, h2⟩) hb
  rw [proj_restrict, proj_eq_mk_of_dvd (dvd_mul_right (cyclotomic 1 ℤ ^ k) (cyclotomic 2 ℤ ^ k))
    hp.symm, AlgHom.commutes, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C] at ha'
  rw [proj_restrict, proj_eq_mk_of_dvd (dvd_mul_left (cyclotomic 2 ℤ ^ k) (cyclotomic 1 ℤ ^ k))
    hp.symm, AlgHom.commutes, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C] at hb'
  exact ⟨p, by simpa [cyclotomic_one] using AdjoinRoot.mk_eq_mk.mp ha',
    by simpa [cyclotomic_two] using AdjoinRoot.mk_eq_mk.mp hb'⟩

/-- The constants `0` on `{1}` and `1` on `{2}` are not the coordinates of an element of the
finite-subset limit: their residues modulo `(Φ₁, Φ₂) = (2, q - 1)` disagree. -/
example : ¬∃ y : FiniteSubsetLimit ℤ {1, 2},
    FiniteSubsetLimit.proj ⟨{1}, by simp, Set.finite_singleton 1⟩ y = 0 ∧
      FiniteSubsetLimit.proj ⟨{2}, by simp, Set.finite_singleton 2⟩ y = 1 := by
  rintro ⟨y, h1, h2⟩
  let U : {U : Set ℕ // U ⊆ {1, 2} ∧ U.Finite} := ⟨{1, 2}, subset_rfl, Set.toFinite _⟩
  obtain ⟨p, ⟨u, hu⟩, ⟨v, hv⟩⟩ :=
    exists_poly_of_restrict_one_two (FiniteSubsetLimit.proj U y) 0 1 1
      ((FiniteSubsetLimit.restrict_proj (U := ⟨{1}, by simp, Set.finite_singleton 1⟩) (V := U)
        (by simp [U]) y).trans (h1.trans (map_zero _).symm))
      ((FiniteSubsetLimit.restrict_proj (U := ⟨{2}, by simp, Set.finite_singleton 2⟩) (V := U)
        (by simp [U]) y).trans (h2.trans (map_one _).symm))
  have hu1 := congrArg (eval 1) hu
  have hv1 := congrArg (eval 1) hv
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_add, eval_one] at hu1 hv1
  omega

/-- The constants `0` on `{1}` and `2` on `{2}` agree modulo `(Φ₁, Φ₂) = (2, q - 1)`, but they are
still not the coordinates of an element of the finite-subset limit: their first jets disagree. -/
example : ¬∃ y : FiniteSubsetLimit ℤ {1, 2},
    FiniteSubsetLimit.proj ⟨{1}, by simp, Set.finite_singleton 1⟩ y = 0 ∧
      FiniteSubsetLimit.proj ⟨{2}, by simp, Set.finite_singleton 2⟩ y = 2 := by
  rintro ⟨y, h1, h2⟩
  let U : {U : Set ℕ // U ⊆ {1, 2} ∧ U.Finite} := ⟨{1, 2}, subset_rfl, Set.toFinite _⟩
  obtain ⟨p, ⟨u, hu⟩, ⟨v, hv⟩⟩ :=
    exists_poly_of_restrict_one_two (FiniteSubsetLimit.proj U y) 0 2 2
      ((FiniteSubsetLimit.restrict_proj (U := ⟨{1}, by simp, Set.finite_singleton 1⟩) (V := U)
        (by simp [U]) y).trans (h1.trans (map_zero _).symm))
      ((FiniteSubsetLimit.restrict_proj (U := ⟨{2}, by simp, Set.finite_singleton 2⟩) (V := U)
        (by simp [U]) y).trans (h2.trans (map_ofNat _ 2).symm))
  have hu1 := congrArg (eval 1) hu
  have hv1 := congrArg (eval 1) hv
  simp only [eval_sub, eval_mul, eval_pow, eval_X, eval_C, eval_add, eval_one] at hu1 hv1
  omega

end TauCeti

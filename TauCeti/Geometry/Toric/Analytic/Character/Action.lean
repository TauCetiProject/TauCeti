/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.AddChar
public import Mathlib.Topology.Algebra.ConstMulAction
public import TauCeti.Geometry.Toric.Analytic.RegularChart
public import TauCeti.Geometry.Toric.Analytic.Torus.Topology

/-!
# The character action on the complex points of an affine semigroup

The complex points of an affine semigroup `S` are the algebra homomorphisms `ℂ[S] →ₐ[ℂ] ℂ`, that
is, the multiplicative characters `S → ℂ`. The invertible characters `AddChar S ℂˣ` form a
commutative monoid under pointwise multiplication, and they act on the complex points by
multiplying values: the point `t • x` takes the value `t s * x (χ ^ s)` on the monomial of `s`.

For the dual semigroup `S = σ^∨ ∩ M` of a toric cone in the character lattice `M = N →+ ℤ`, the
coordinate-free complex torus `AddChar M ℂˣ` acts through restriction of characters to `S`. This
file records that restricted action for an arbitrary submonoid `S` of an additive monoid `M`, so
that the torus of the lattice acts on every affine chart and the face-localization maps between
charts are equivariant.

The distinguished complex point, which takes the value `1` on every monomial, has trivial
stabilizer, and its orbit under the invertible characters of `S` is exactly the locus where no
monomial vanishes. For a split semigroup `S ≃+ (ι →₀ ℕ) × (κ →₀ ℤ)`, this locus is the set of
points whose unconstrained coordinates are all nonzero; it is open and dense in the complex points
of `S`, and the action is coordinatewise multiplication. These are the affine pieces of the dense
torus of a toric variety.

Translation by a fixed character is a homeomorphism for the monomial-embedding topology of any
finite generating family, packaged as a `ContinuousConstSMul` fact so that Mathlib's
`Homeomorph.smul` applies. The coordinate-free complex torus also acts jointly continuously on
the complex points of any submonoid of its character lattice.

## Main declarations

* `TauCeti.Toric.AffineSemigroupComplexPoint.instMulActionAddCharUnitsComplex`: the action of the
  invertible characters of `S` on its complex points, with
  `TauCeti.Toric.AffineSemigroupComplexPoint.smul_apply_single` computing it on monomials.
* `TauCeti.Toric.AffineSemigroupComplexPoint.instMulActionAddCharUnitsComplexSubtypeMem`: the
  action of the invertible characters of an ambient monoid on the complex points of a submonoid,
  through restriction, with `TauCeti.Toric.AffineSemigroupComplexPoint.ambient_smul_apply_single`.
* `TauCeti.Toric.AffineSemigroupComplexPoint.comap_smul` and
  `TauCeti.Toric.AffineSemigroupComplexPoint.comap_inclusion_smul`: the maps on complex points
  induced by semigroup homomorphisms are equivariant.
* `TauCeti.Toric.AffineSemigroupComplexPoint.mem_orbit_default_iff`: the orbit of the distinguished
  point is the locus where no monomial vanishes, and
  `TauCeti.Toric.AffineSemigroupComplexPoint.smul_default_injective`: the characters act freely
  on it.
* `TauCeti.Toric.AffineSemigroupComplexPoint.continuousConstSMul_affinePointTopology`:
  translation by a character is continuous for the monomial-embedding topology, and
  `TauCeti.Toric.AffineSemigroupComplexPoint.isOpen_orbit_default`: the orbit of the distinguished
  point is open.
* `TauCeti.Toric.AffineSemigroupComplexPoint.continuousSMul_affinePointTopology_complexTorus`:
  the complex torus acts jointly continuously on the complex points of any finitely generated
  submonoid of its character lattice.
* `TauCeti.Toric.regularAffinePointEquiv_smul_fst` and
  `TauCeti.Toric.regularAffinePointEquiv_smul_snd`: in the mixed coordinates of a split semigroup
  the action is coordinatewise multiplication;
  `TauCeti.Toric.mem_orbit_default_iff_regularAffinePointEquiv` and
  `TauCeti.Toric.dense_orbit_default`: the orbit of the distinguished point is the locus where the
  unconstrained coordinates are nonzero, which is dense.

## References

* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §§1.1 and 3.2.
* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 2.1.
-/

public section

open Multiplicative Topology

namespace TauCeti.Toric

variable {S T : Type*} [AddCommMonoid S] [AddCommMonoid T] {r : ℕ}

namespace AffineSemigroupComplexPoint

/-! ### The action of the invertible characters of the semigroup -/

/-- An invertible character `t : AddChar S ℂˣ` acts on a complex point `x` of `S` by multiplying
its values: `t • x` sends the monomial of `s` to `t s * x (χ ^ s)`. -/
noncomputable instance : SMul (AddChar S ℂˣ) (AffineSemigroupComplexPoint S) where
  smul t x := MonoidAlgebra.lift ℂ ℂ (Multiplicative S)
    ((Units.coeHom ℂ).comp t.toMonoidHom * (MonoidAlgebra.lift ℂ ℂ (Multiplicative S)).symm x)

/-- The twisted point, as the algebra homomorphism induced by the pointwise product of the
character and the multiplicative character underlying the point. -/
theorem smul_def (t : AddChar S ℂˣ) (x : AffineSemigroupComplexPoint S) :
    t • x = MonoidAlgebra.lift ℂ ℂ (Multiplicative S)
      ((Units.coeHom ℂ).comp t.toMonoidHom * (MonoidAlgebra.lift ℂ ℂ (Multiplicative S)).symm x) :=
  (rfl)

/-- The twisted point takes the product of the character value and the original value on every
monomial. -/
@[simp]
theorem smul_apply_single (t : AddChar S ℂˣ) (x : AffineSemigroupComplexPoint S) (s : S) :
    (t • x) (MonoidAlgebra.single (ofAdd s) 1) = t s * x (MonoidAlgebra.single (ofAdd s) 1) := by
  rw [smul_def, MonoidAlgebra.lift_single, one_smul, MonoidHom.mul_apply, MonoidHom.comp_apply,
    Units.coeHom_apply, AddChar.toMonoidHom_apply, toAdd_ofAdd, MonoidAlgebra.lift_symm_apply]

/-- The invertible characters of `S` act on the complex points of `S`. -/
noncomputable instance : MulAction (AddChar S ℂˣ) (AffineSemigroupComplexPoint S) where
  one_smul x := AffineSemigroupComplexPoint.ext fun s ↦ by simp
  mul_smul t t' x := AffineSemigroupComplexPoint.ext fun s ↦ by simp [mul_assoc]

/-- Pulling back along a semigroup homomorphism is equivariant, the character being restricted
along the homomorphism. -/
theorem comap_smul (f : S →+ T) (t : AddChar T ℂˣ) (x : AffineSemigroupComplexPoint T) :
    comap f (t • x) = t.compAddMonoidHom f • comap f x :=
  AffineSemigroupComplexPoint.ext fun s ↦ by simp

/-! ### The orbit of the distinguished point -/

/-- The invertible characters act freely on the distinguished point: it has trivial stabilizer. -/
theorem smul_default_injective :
    Function.Injective fun t : AddChar S ℂˣ ↦ t • (default : AffineSemigroupComplexPoint S) := by
  intro t t' h
  refine AddChar.ext _ _ fun s ↦ Units.ext ?_
  simpa using
    congrArg (fun x : AffineSemigroupComplexPoint S ↦ x (MonoidAlgebra.single (ofAdd s) 1)) h

/-- The orbit of the distinguished point under the invertible characters is the locus of complex
points at which no monomial vanishes: such a point is itself an invertible character. -/
theorem mem_orbit_default_iff {x : AffineSemigroupComplexPoint S} :
    x ∈ MulAction.orbit (AddChar S ℂˣ) (default : AffineSemigroupComplexPoint S) ↔
      ∀ s : S, x (MonoidAlgebra.single (ofAdd s) 1) ≠ 0 := by
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨t, rfl⟩ s
    simp
  · refine ⟨⟨fun s ↦ Units.mk0 _ (h s), Units.ext ?_, fun s s' ↦ Units.ext ?_⟩, ?_⟩
    · simp [← MonoidAlgebra.one_def]
    · have hs : MonoidAlgebra.single (ofAdd (s + s')) (1 : ℂ) =
          MonoidAlgebra.single (ofAdd s) 1 * MonoidAlgebra.single (ofAdd s') 1 := by
        rw [MonoidAlgebra.single_mul_single, one_mul, ofAdd_add]
      simp only [Units.val_mul, Units.val_mk0]
      rw [hs, map_mul]
    · exact AffineSemigroupComplexPoint.ext fun s ↦ by simp

/-! ### Continuity -/

/-- Translation by a fixed character is continuous for the monomial-embedding topology of any
finite generating family: it multiplies every monomial value by a constant. -/
theorem continuous_const_smul_affinePointTopology (g : AddGeneratingFamily S r)
    (t : AddChar S ℂˣ) :
    Continuous[affinePointTopology g, affinePointTopology g]
      fun x : AffineSemigroupComplexPoint S ↦ t • x := by
  -- install the monomial-embedding topology as an instance so that the continuity combinators apply
  let _ := affinePointTopology g
  rw [continuous_iff_forall_continuous_apply_single]
  intro s
  simp only [smul_apply_single]
  exact continuous_const.mul (continuous_apply_single g s)

/-- The invertible characters act by homeomorphisms for the monomial-embedding topology of any
finite generating family. -/
theorem continuousConstSMul_affinePointTopology (g : AddGeneratingFamily S r) :
    letI := affinePointTopology g
    ContinuousConstSMul (AddChar S ℂˣ) (AffineSemigroupComplexPoint S) :=
  letI := affinePointTopology g
  ⟨continuous_const_smul_affinePointTopology g⟩

/-- The orbit of the distinguished point is open for the monomial-embedding topology of any
finite generating family: it is the locus where the finitely many coordinates of the embedding are
all nonzero. -/
theorem isOpen_orbit_default (g : AddGeneratingFamily S r) :
    IsOpen[affinePointTopology g]
      (MulAction.orbit (AddChar S ℂˣ) (default : AffineSemigroupComplexPoint S)) := by
  let _ := affinePointTopology g
  have h : MulAction.orbit (AddChar S ℂˣ) (default : AffineSemigroupComplexPoint S) =
      ⋂ j, {x | monomialEmbedding g x j ≠ 0} := by
    ext x
    simp only [mem_orbit_default_iff, Set.mem_iInter, Set.mem_ofPred_eq]
    refine ⟨fun h j ↦ by rw [monomialEmbedding_apply]; exact h _, fun h s ↦ ?_⟩
    obtain ⟨a, ha⟩ := AddSubmonoid.exists_of_mem_closure_range g.toFun s (by
      rw [g.spans]
      trivial)
    rw [apply_single_eq_prod_monomialEmbedding g ha]
    exact Finset.prod_ne_zero_iff.2 fun j _ ↦ pow_ne_zero _ (h j)
  rw [h]
  exact isOpen_iInter_of_finite fun j ↦
    isOpen_ne.preimage ((continuous_apply j).comp (continuous_monomialEmbedding g))

/-! ### The action of the characters of an ambient monoid -/

section Ambient

variable {M : Type*} [AddCommMonoid M] {S S' : AddSubmonoid M}

/-- The invertible characters of an ambient monoid `M` act on the complex points of a submonoid
`S ≤ M` through restriction of characters to `S`. For the dual semigroup of a toric cone in the
character lattice `N →+ ℤ`, this is the action of the coordinate-free complex torus on the affine
chart of the cone. -/
noncomputable instance : SMul (AddChar M ℂˣ) (AffineSemigroupComplexPoint S) where
  smul t x := t.compAddMonoidHom S.subtype • x

/-- The ambient characters act through their restriction to the submonoid. -/
theorem ambient_smul_def (t : AddChar M ℂˣ) (x : AffineSemigroupComplexPoint S) :
    t • x = t.compAddMonoidHom S.subtype • x :=
  (rfl)

/-- The ambient characters act through their values on the elements of the submonoid. -/
@[simp]
theorem ambient_smul_apply_single (t : AddChar M ℂˣ) (x : AffineSemigroupComplexPoint S) (s : S) :
    (t • x) (MonoidAlgebra.single (ofAdd s) 1) = t s * x (MonoidAlgebra.single (ofAdd s) 1) := by
  rw [ambient_smul_def, smul_apply_single, AddChar.compAddMonoidHom_apply,
    AddSubmonoid.coe_subtype]

/-- The invertible characters of an ambient monoid act on the complex points of a submonoid. -/
noncomputable instance : MulAction (AddChar M ℂˣ) (AffineSemigroupComplexPoint S) where
  one_smul x := AffineSemigroupComplexPoint.ext fun s ↦ by simp
  mul_smul t t' x := AffineSemigroupComplexPoint.ext fun s ↦ by simp [mul_assoc]

/-- The map on complex points induced by an inclusion of submonoids is equivariant for the
ambient characters. -/
theorem comap_inclusion_smul (h : S ≤ S') (t : AddChar M ℂˣ)
    (x : AffineSemigroupComplexPoint S') :
    comap (AddSubmonoid.inclusion h) (t • x) = t • comap (AddSubmonoid.inclusion h) x :=
  AffineSemigroupComplexPoint.ext fun s ↦ by simp

/-- The orbit of the distinguished point under the ambient characters is contained in its orbit
under the invertible characters of the submonoid. The two orbits agree when every invertible
character of the submonoid is the restriction of an ambient one, as for the dual semigroup of a
toric cone with an extending basis. -/
theorem orbit_default_subset (S : AddSubmonoid M) :
    MulAction.orbit (AddChar M ℂˣ) (default : AffineSemigroupComplexPoint S) ⊆
      MulAction.orbit (AddChar S ℂˣ) (default : AffineSemigroupComplexPoint S) := by
  rintro _ ⟨t, rfl⟩
  exact ⟨t.compAddMonoidHom S.subtype, (ambient_smul_def t default).symm⟩

/-- Translation by a fixed ambient character is continuous for the monomial-embedding topology
of any finite generating family. -/
theorem continuousConstSMul_affinePointTopology_ambient (g : AddGeneratingFamily S r) :
    letI := affinePointTopology g
    ContinuousConstSMul (AddChar M ℂˣ) (AffineSemigroupComplexPoint S) :=
  letI := affinePointTopology g
  ⟨fun t ↦ continuous_const_smul_affinePointTopology g (t.compAddMonoidHom S.subtype)⟩

end Ambient

/-- The torus acts jointly continuously on the complex points of a submonoid of the character
lattice, for the monomial-embedding topology of any finite generating family. -/
theorem continuousSMul_affinePointTopology_complexTorus {N : Type*} [AddCommGroup N]
    {S : AddSubmonoid (IntegralCharacter N)} (g : AddGeneratingFamily S r) :
    letI := affinePointTopology g
    ContinuousSMul (ComplexTorus N) (AffineSemigroupComplexPoint S) := by
  let _ := affinePointTopology g
  refine ⟨(continuous_iff_forall_continuous_apply_single g _).2 fun s ↦ ?_⟩
  simp only [ambient_smul_apply_single]
  exact (Units.continuous_val.comp ((continuous_complexTorus_apply (s : IntegralCharacter N)).comp
    continuous_fst)).mul ((continuous_apply_single g s).comp continuous_snd)

end AffineSemigroupComplexPoint

/-! ### The action in mixed coordinates -/

section Regular

open AffineSemigroupComplexPoint

variable {ι κ : Type*}

/-- In the mixed coordinates of a split semigroup, a character multiplies each unconstrained
coordinate by its value on the corresponding standard generator. -/
theorem regularAffinePointEquiv_smul_fst (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ))) (t : AddChar S ℂˣ)
    (x : AffineSemigroupComplexPoint S) (i : ι) :
    (regularAffinePointEquiv e (t • x)).1 i =
      t (e.symm (Finsupp.single i 1, 0)) * (regularAffinePointEquiv e x).1 i := by
  simp

/-- In the mixed coordinates of a split semigroup, a character multiplies each invertible
coordinate by its value on the corresponding standard generator. -/
theorem regularAffinePointEquiv_smul_snd (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ))) (t : AddChar S ℂˣ)
    (x : AffineSemigroupComplexPoint S) (j : κ) :
    (regularAffinePointEquiv e (t • x)).2 j =
      t (e.symm (0, Finsupp.single j 1)) * (regularAffinePointEquiv e x).2 j :=
  Units.ext (by simp)

/-- The distinguished point has all mixed coordinates equal to `1`. -/
@[simp]
theorem regularAffinePointEquiv_default (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ))) :
    regularAffinePointEquiv e (default : AffineSemigroupComplexPoint S) = 1 :=
  Prod.ext (funext fun i ↦ by simp) (funext fun j ↦ Units.ext (by simp))

/-- In mixed coordinates, the orbit of the distinguished point is the locus where every
unconstrained coordinate is nonzero. -/
theorem mem_orbit_default_iff_regularAffinePointEquiv (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ)))
    {x : AffineSemigroupComplexPoint S} :
    x ∈ MulAction.orbit (AddChar S ℂˣ) (default : AffineSemigroupComplexPoint S) ↔
      ∀ i, (regularAffinePointEquiv e x).1 i ≠ 0 := by
  rw [mem_orbit_default_iff]
  refine ⟨fun h i ↦ by simpa using h (e.symm (Finsupp.single i 1, 0)), fun h s ↦ ?_⟩
  have hx := regularAffinePointEquiv_symm_apply_single e (regularAffinePointEquiv e x) s
  rw [Equiv.symm_apply_apply] at hx
  rw [hx]
  exact mul_ne_zero (Finsupp.prod_ne_zero_iff.2 fun i _ ↦ pow_ne_zero _ (h i)) (Units.ne_zero _)

/-- The orbit of the distinguished point is dense in the complex points of a split semigroup, for
the monomial-embedding topology of any finite generating family: in mixed coordinates it is the
locus where the unconstrained coordinates are nonzero. -/
theorem dense_orbit_default (g : AddGeneratingFamily S r) (e : S ≃+ ((ι →₀ ℕ) × (κ →₀ ℤ))) :
    @Dense _ (affinePointTopology g)
      (MulAction.orbit (AddChar S ℂˣ) (default : AffineSemigroupComplexPoint S)) := by
  let _ := affinePointTopology g
  have h : MulAction.orbit (AddChar S ℂˣ) (default : AffineSemigroupComplexPoint S) =
      regularAffinePointHomeomorph g e ⁻¹'
        (Set.pi Set.univ (fun _ : ι ↦ {(0 : ℂ)}ᶜ) ×ˢ Set.univ) := by
    ext x
    simp [mem_orbit_default_iff_regularAffinePointEquiv e]
  rw [h]
  exact ((dense_pi Set.univ fun _ _ ↦ dense_compl_singleton 0).prod dense_univ).preimage
    (regularAffinePointHomeomorph g e).isOpenMap

end Regular

end TauCeti.Toric

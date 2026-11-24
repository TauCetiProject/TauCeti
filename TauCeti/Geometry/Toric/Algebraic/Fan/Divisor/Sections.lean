/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import TauCeti.Algebra.MonoidAlgebra.Supported
public import TauCeti.Geometry.Toric.Algebraic.Fan.Divisor.Weights

import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Face

/-!
# Monomial sections of toric divisors

For integer ray coefficients `a` on a fan `Phi`, the global monomial section module for `a`
consists of Laurent polynomials supported on `Phi.divisorWeights a`. The module on a cone
uses only the rays of that cone. Both lie in the same character algebra, so restriction to a
face retains each coefficient and gluing means agreement in that algebra. The support
conditions are independent of the coefficient semiring, and convolution adds divisors.
Restriction to a face is localization at its exposing monomial. A local Cartier character
trivializes the section module over the chart ring.

## References

* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §8, Definition/Proposition 8.4.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, Proposition 4.3.3.
-/

public section

noncomputable section

open AddMonoidAlgebra
open scoped Pointwise TensorProduct

namespace TauCeti.Toric.Fan

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V] {i : N →+ V}
  (Phi : Fan i) (R : Type*)

section Sections

variable [Semiring R]

/-- Finite sums of characters satisfying the divisor inequalities on every ray of the fan. -/
abbrev divisorSections (a : Phi.Ray → ℤ) : Submodule R (AddMonoidAlgebra R (N →+ ℤ)) :=
  supported R R (Phi.divisorWeights a)

/-- Finite sums of characters satisfying the divisor inequalities on the rays of a cone. -/
abbrev coneDivisorSections (sigma : Phi.cones) (a : Phi.Ray → ℤ) :
    Submodule R (AddMonoidAlgebra R (N →+ ℤ)) :=
  supported R R (Phi.coneDivisorWeights sigma a)

variable {Phi R}

/-- Global sections are exactly the Laurent polynomials satisfying the support conditions on
every chart. -/
theorem divisorSections_eq_iInf (a : Phi.Ray → ℤ) :
    Phi.divisorSections R a = ⨅ sigma : Phi.cones, Phi.coneDivisorSections R sigma a := by
  ext f
  simp only [Submodule.mem_iInf, mem_supported]
  rw [← Phi.iInter_coneDivisorWeights a, Set.subset_iInter_iff]

/-- Restrict a global monomial section to a chart, retaining its coefficients. -/
def divisorSectionsRestrict (sigma : Phi.cones) (a : Phi.Ray → ℤ) :
    Phi.divisorSections R a →ₗ[R] Phi.coneDivisorSections R sigma a :=
  Submodule.inclusion (supported_mono (Phi.divisorWeights_subset_coneDivisorWeights sigma a))

/-- Global restriction is the inclusion into the chart module in the character algebra. -/
@[simp]
theorem coe_divisorSectionsRestrict (sigma : Phi.cones) {a : Phi.Ray → ℤ}
    (f : Phi.divisorSections R a) :
    (divisorSectionsRestrict sigma a f : AddMonoidAlgebra R (N →+ ℤ)) = f :=
  (rfl)

/-- Restriction to a face retains the coefficients and drops the inequalities on rays outside
the face. -/
def coneDivisorSectionsRestrict {sigma tau : Phi.cones} (h : tau ≤ sigma) (a : Phi.Ray → ℤ) :
    Phi.coneDivisorSections R sigma a →ₗ[R] Phi.coneDivisorSections R tau a :=
  Submodule.inclusion (supported_mono (coneDivisorWeights_anti h a))

/-- Face restriction is the inclusion into the face module in the character algebra. -/
@[simp]
theorem coe_coneDivisorSectionsRestrict {sigma tau : Phi.cones} (h : tau ≤ sigma)
    {a : Phi.Ray → ℤ} (f : Phi.coneDivisorSections R sigma a) :
    (coneDivisorSectionsRestrict h a f : AddMonoidAlgebra R (N →+ ℤ)) = f :=
  (rfl)

/-- Changing coefficients commutes with restriction from the fan to a chart. -/
@[simp]
theorem supportedMap_divisorSectionsRestrict {S : Type*} [Semiring S] (φ : R →+* S)
    (sigma : Phi.cones) {a : Phi.Ray → ℤ} (f : Phi.divisorSections R a) :
    supportedMap _ φ (divisorSectionsRestrict sigma a f) =
      divisorSectionsRestrict sigma a (supportedMap _ φ f) := by
  apply Subtype.ext
  simp only [coe_supportedMap, coe_divisorSectionsRestrict]

/-- Changing coefficients commutes with restriction from a cone to a face. -/
@[simp]
theorem supportedMap_coneDivisorSectionsRestrict {S : Type*} [Semiring S] (φ : R →+* S)
    {sigma tau : Phi.cones} (h : tau ≤ sigma) {a : Phi.Ray → ℤ}
    (f : Phi.coneDivisorSections R sigma a) :
    supportedMap _ φ (coneDivisorSectionsRestrict h a f) =
      coneDivisorSectionsRestrict h a (supportedMap _ φ f) := by
  apply Subtype.ext
  simp only [coe_supportedMap, coe_coneDivisorSectionsRestrict]

@[simp]
theorem coneDivisorSectionsRestrict_refl (sigma : Phi.cones) (a : Phi.Ray → ℤ) :
    coneDivisorSectionsRestrict (R := R) (le_refl sigma) a = LinearMap.id := by
  ext f : 1
  apply Subtype.ext
  simp

@[simp]
theorem coneDivisorSectionsRestrict_comp {sigma tau upsilon : Phi.cones} (h : tau ≤ sigma)
    (k : upsilon ≤ tau) (a : Phi.Ray → ℤ) :
    (coneDivisorSectionsRestrict (R := R) k a).comp (coneDivisorSectionsRestrict h a) =
      coneDivisorSectionsRestrict (k.trans h) a := by
  ext f : 1
  apply Subtype.ext
  simp

@[simp]
theorem coneDivisorSectionsRestrict_comp_divisorSectionsRestrict
    {sigma tau : Phi.cones} (h : tau ≤ sigma) (a : Phi.Ray → ℤ) :
    (coneDivisorSectionsRestrict (R := R) h a).comp (divisorSectionsRestrict sigma a) =
      divisorSectionsRestrict tau a := by
  ext f : 1
  apply Subtype.ext
  simp

/-- A family of monomial sections agreeing on pairwise overlaps of a nonempty fan has a unique
global monomial section. -/
theorem existsUnique_divisorSections_of_agree [Nonempty Phi.cones] {a : Phi.Ray → ℤ}
    (f : ∀ sigma : Phi.cones, Phi.coneDivisorSections R sigma a)
    (h : ∀ sigma tau,
      coneDivisorSectionsRestrict (inf_le_left : sigma ⊓ tau ≤ sigma) a (f sigma) =
      coneDivisorSectionsRestrict (inf_le_right : sigma ⊓ tau ≤ tau) a (f tau)) :
    ∃! g : Phi.divisorSections R a, ∀ sigma, divisorSectionsRestrict sigma a g = f sigma := by
  obtain ⟨sigma₀⟩ := ‹Nonempty Phi.cones›
  have hagree (tau : Phi.cones) :
      (f sigma₀ : AddMonoidAlgebra R (N →+ ℤ)) = f tau := by
    simpa using congrArg Subtype.val (h sigma₀ tau)
  have hmem : (f sigma₀ : AddMonoidAlgebra R (N →+ ℤ)) ∈ Phi.divisorSections R a := by
    rw [divisorSections_eq_iInf, Submodule.mem_iInf]
    intro tau
    rw [hagree tau]
    exact (f tau).property
  refine ⟨⟨f sigma₀, hmem⟩, fun tau ↦ Subtype.ext ?_, fun g hg ↦ Subtype.ext ?_⟩
  · simpa only [coe_divisorSectionsRestrict] using hagree tau
  · simpa only [coe_divisorSectionsRestrict] using congrArg Subtype.val (hg sigma₀)

end Sections

variable {Phi R}

/-- The global section modules multiply by addition of divisors, with the unit in the zero
divisor's module. This gives associative products on the graded monoid of sections. -/
instance instGradedMonoidDivisorSections [Semiring R] (Phi : Fan i) :
    SetLike.GradedMonoid (Phi.divisorSections R) :=
  gradedMonoid_supported _ (zero_mem_divisorWeights_iff.2 le_rfl) Phi.divisorWeights_add_subset

/-- The chart section modules multiply by addition of divisors, with the unit in the zero
divisor's module. -/
instance instGradedMonoidConeDivisorSections [Semiring R] (sigma : Phi.cones) :
    SetLike.GradedMonoid (Phi.coneDivisorSections R sigma) :=
  gradedMonoid_supported _ (by
    rw [coneDivisorWeights_zero]
    exact (dualSemigroup Phi.lattice sigma.val).zero_mem) (Phi.coneDivisorWeights_add_subset sigma)

section Multiplication

variable [CommSemiring R]

/-- Convolution of global monomial sections adds the ray coefficients of the divisors. -/
def divisorSectionsMul (a b : Phi.Ray → ℤ) :
    Phi.divisorSections R a →ₗ[R] Phi.divisorSections R b →ₗ[R] Phi.divisorSections R (a + b) :=
  supportedMul (Phi.divisorWeights_add_subset a b)

@[simp]
theorem coe_divisorSectionsMul {a b : Phi.Ray → ℤ}
    (f : Phi.divisorSections R a) (g : Phi.divisorSections R b) :
    (divisorSectionsMul a b f g : AddMonoidAlgebra R (N →+ ℤ)) = f.val * g.val :=
  coe_supportedMul _ _ _

/-- Convolution on one chart adds the ray coefficients of the divisors. -/
def coneDivisorSectionsMul (sigma : Phi.cones) (a b : Phi.Ray → ℤ) :
    Phi.coneDivisorSections R sigma a →ₗ[R] Phi.coneDivisorSections R sigma b →ₗ[R]
      Phi.coneDivisorSections R sigma (a + b) :=
  supportedMul (Phi.coneDivisorWeights_add_subset sigma a b)

@[simp]
theorem coe_coneDivisorSectionsMul {sigma : Phi.cones} {a b : Phi.Ray → ℤ}
    (f : Phi.coneDivisorSections R sigma a) (g : Phi.coneDivisorSections R sigma b) :
    (coneDivisorSectionsMul sigma a b f g : AddMonoidAlgebra R (N →+ ℤ)) = f.val * g.val :=
  coe_supportedMul _ _ _

/-- Multiplication of sections as a linear map on the tensor product of global modules. -/
def divisorSectionsTensorMul (a b : Phi.Ray → ℤ) :
    Phi.divisorSections R a ⊗[R] Phi.divisorSections R b →ₗ[R] Phi.divisorSections R (a + b) :=
  TensorProduct.lift (divisorSectionsMul a b)

@[simp]
theorem divisorSectionsTensorMul_tmul {a b : Phi.Ray → ℤ}
    (f : Phi.divisorSections R a) (g : Phi.divisorSections R b) :
    divisorSectionsTensorMul a b (f ⊗ₜ[R] g) = divisorSectionsMul a b f g :=
  TensorProduct.lift.tmul ..

/-- Multiplication of sections as a linear map on the tensor product of two chart modules. -/
def coneDivisorSectionsTensorMul (sigma : Phi.cones) (a b : Phi.Ray → ℤ) :
    Phi.coneDivisorSections R sigma a ⊗[R] Phi.coneDivisorSections R sigma b →ₗ[R]
      Phi.coneDivisorSections R sigma (a + b) :=
  TensorProduct.lift (coneDivisorSectionsMul sigma a b)

@[simp]
theorem coneDivisorSectionsTensorMul_tmul {sigma : Phi.cones} {a b : Phi.Ray → ℤ}
    (f : Phi.coneDivisorSections R sigma a) (g : Phi.coneDivisorSections R sigma b) :
    coneDivisorSectionsTensorMul sigma a b (f ⊗ₜ[R] g) = coneDivisorSectionsMul sigma a b f g :=
  TensorProduct.lift.tmul ..

/-- Restriction to a chart commutes with convolution of monomial sections. -/
@[simp]
theorem divisorSectionsRestrict_divisorSectionsMul (sigma : Phi.cones) {a b : Phi.Ray → ℤ}
    (f : Phi.divisorSections R a) (g : Phi.divisorSections R b) :
    divisorSectionsRestrict sigma (a + b) (divisorSectionsMul a b f g) =
      coneDivisorSectionsMul sigma a b (divisorSectionsRestrict sigma a f)
        (divisorSectionsRestrict sigma b g) := by
  apply Subtype.ext
  simp

/-- Face restriction commutes with convolution of monomial sections. -/
@[simp]
theorem coneDivisorSectionsRestrict_coneDivisorSectionsMul {sigma tau : Phi.cones} (h : tau ≤ sigma)
    {a b : Phi.Ray → ℤ} (f : Phi.coneDivisorSections R sigma a)
    (g : Phi.coneDivisorSections R sigma b) :
    coneDivisorSectionsRestrict h (a + b) (coneDivisorSectionsMul sigma a b f g) =
      coneDivisorSectionsMul tau a b (coneDivisorSectionsRestrict h a f)
        (coneDivisorSectionsRestrict h b g) := by
  apply Subtype.ext
  simp

end Multiplication

section Chart

variable [Semiring R]

/-! ### Modules over the chart rings -/

/-- The chart ring acts on the local section module by multiplication in the Laurent character
algebra. The weights of a local section are stable under adding exponents of the chart ring. -/
instance instModuleConeDivisorSections (sigma : Phi.cones) (a : Phi.Ray → ℤ) :
    Module (AddMonoidAlgebra R (dualSemigroup Phi.lattice sigma.val))
      (Phi.coneDivisorSections R sigma a) :=
  AddSubmonoid.supportedModule _ (dualSemigroup_add_coneDivisorWeights_subset sigma a)

/-- Changing coefficients commutes with the action of the chart ring on sections. -/
@[simp]
theorem supportedMap_smul_coneDivisorSections {S : Type*} [Semiring S] (φ : R →+* S)
    {sigma : Phi.cones} {a : Phi.Ray → ℤ}
    (g : AddMonoidAlgebra R (dualSemigroup Phi.lattice sigma.val))
    (f : Phi.coneDivisorSections R sigma a) :
    supportedMap (Phi.coneDivisorWeights sigma a) φ (g • f) =
      mapRingHom _ φ g • supportedMap _ φ f := by
  apply Subtype.ext
  simp only [coe_supportedMap, AddSubmonoid.coe_smul_supportedModule, ← coe_mapRingHom, map_mul]
  rw [← RingHom.comp_apply, mapRingHom_comp_mapDomainRingHom, RingHom.comp_apply]

/-- Multiplication by the Cartier character trivializes the local section module over the chart
ring. The character has value `-a ρ` on each ray of the chart. -/
def coneDivisorSectionsCartierEquiv {sigma : Phi.cones} {a : Phi.Ray → ℤ} {m : N →+ ℤ}
    (hm : ∀ rho : Phi.Ray, rho.toCone ≤ sigma → m rho.primitiveGenerator = -a rho) :
    AddMonoidAlgebra R (dualSemigroup Phi.lattice sigma.val) ≃ₗ[
      AddMonoidAlgebra R (dualSemigroup Phi.lattice sigma.val)]
      Phi.coneDivisorSections R sigma a :=
  (dualSemigroup Phi.lattice sigma.val).supportedAddSingletonEquiv (m := m) (by
    rw [coneDivisorWeights_eq_vadd hm, ← Set.image_vadd, add_comm, Set.singleton_add]
    simp only [vadd_eq_add])

/-- The Cartier frame sends a chart function to its product with the frame monomial. -/
@[simp]
theorem coe_coneDivisorSectionsCartierEquiv
    {sigma : Phi.cones} {a : Phi.Ray → ℤ} {m : N →+ ℤ}
    (hm : ∀ rho : Phi.Ray, rho.toCone ≤ sigma → m rho.primitiveGenerator = -a rho)
    (g : AddMonoidAlgebra R (dualSemigroup Phi.lattice sigma.val)) :
    (coneDivisorSectionsCartierEquiv hm g : AddMonoidAlgebra R (N →+ ℤ)) =
      mapDomainRingHom R (dualSemigroup Phi.lattice sigma.val).subtype g * single m 1 :=
  AddSubmonoid.coe_supportedAddSingletonEquiv _ _ g

/-- The inverse Cartier frame recovers the chart coordinate by multiplying by the inverse
monomial in the character algebra. -/
@[simp]
theorem mapDomain_coneDivisorSectionsCartierEquiv_symm
    {sigma : Phi.cones} {a : Phi.Ray → ℤ} {m : N →+ ℤ}
    (hm : ∀ rho : Phi.Ray, rho.toCone ≤ sigma → m rho.primitiveGenerator = -a rho)
    (f : Phi.coneDivisorSections R sigma a) :
    mapDomain Subtype.val
        ((coneDivisorSectionsCartierEquiv hm).symm f) = f.val * single (-m) 1 :=
  AddSubmonoid.mapDomain_supportedAddSingletonEquiv_symm _ _ f

/-! ### Clearing denominators on a face -/

/-- A section on a face becomes a section on the larger chart after multiplication by a
sufficiently large power of the monomial exposing the face. -/
theorem exists_pow_mul_mem_coneDivisorSections {sigma tau : Phi.cones} {m : N →+ ℤ}
    (hm : m ∈ dualSemigroup Phi.lattice sigma.val)
    (htau : sigma.val ⊓
      PointedCone.ofSubmodule (LinearMap.ker (Phi.lattice.realCharacter m)) = tau.val)
    {a : Phi.Ray → ℤ} (f : Phi.coneDivisorSections R tau a) :
    ∃ n : ℕ, single m (1 : R) ^ n * f.val ∈ Phi.coneDivisorSections R sigma a := by
  classical
  obtain ⟨n, hn⟩ := exists_nsmul_add_mem_coneDivisorWeights hm htau
    f.val.coeff.support (mem_supported.1 f.property)
  refine ⟨n, mem_supported.2 fun u hu ↦ ?_⟩
  rw [single_pow, one_pow] at hu
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1
    (support_coeff_single_mul_subset f.val 1 (n • m) hu)
  exact hn v hv

/-- Restricting a scalar multiple sends the chart scalar along the inclusion of dual semigroups. -/
@[simp]
theorem coneDivisorSectionsRestrict_smul {sigma tau : Phi.cones} (h : tau ≤ sigma)
    {a : Phi.Ray → ℤ} (g : AddMonoidAlgebra R (dualSemigroup Phi.lattice sigma.val))
    (f : Phi.coneDivisorSections R sigma a) :
    coneDivisorSectionsRestrict h a (g • f) =
      mapDomainRingHom R (AddSubmonoid.inclusion (dualSemigroup_anti Phi.lattice h)) g •
        coneDivisorSectionsRestrict h a f := by
  apply Subtype.ext
  simp only [coe_coneDivisorSectionsRestrict, AddSubmonoid.coe_smul_supportedModule]
  rw [← RingHom.comp_apply, ← mapDomainRingHom_comp, AddSubmonoid.subtype_comp_inclusion]

/-- Face restriction is linear over the larger cone's chart ring, acting on the face module
through the inclusion of dual semigroups. -/
def coneDivisorSectionsRestrictOverChart {sigma tau : Phi.cones} (h : tau ≤ sigma)
    (a : Phi.Ray → ℤ) :
    letI := Module.compHom (Phi.coneDivisorSections R tau a)
      (mapDomainRingHom R (AddSubmonoid.inclusion (dualSemigroup_anti Phi.lattice h)))
    Phi.coneDivisorSections R sigma a →ₗ[AddMonoidAlgebra R (dualSemigroup Phi.lattice sigma.val)]
      Phi.coneDivisorSections R tau a := by
  letI := Module.compHom (Phi.coneDivisorSections R tau a)
    (mapDomainRingHom R (AddSubmonoid.inclusion (dualSemigroup_anti Phi.lattice h)))
  exact ⟨⟨coneDivisorSectionsRestrict h a, map_add _⟩, coneDivisorSectionsRestrict_smul h⟩

@[simp]
theorem coe_coneDivisorSectionsRestrictOverChart {sigma tau : Phi.cones} (h : tau ≤ sigma)
    {a : Phi.Ray → ℤ} (f : Phi.coneDivisorSections R sigma a) :
    (coneDivisorSectionsRestrictOverChart h a f).val = f.val :=
  (rfl)

end Chart

variable [CommSemiring R]

/-- Restriction to the face cut out by a character is localization of the section module at
the corresponding monomial in the chart ring. -/
theorem isLocalizedModule_coneDivisorSectionsRestrictOverChart {sigma tau : Phi.cones}
    (h : tau ≤ sigma) (m : dualSemigroup Phi.lattice sigma.val)
    (htau : sigma.val ⊓
      PointedCone.ofSubmodule (LinearMap.ker (Phi.lattice.realCharacter m)) = tau.val)
    (a : Phi.Ray → ℤ) :
    letI := Module.compHom (Phi.coneDivisorSections R tau a)
      (mapDomainRingHom R (AddSubmonoid.inclusion (dualSemigroup_anti Phi.lattice h)))
    IsLocalizedModule (Submonoid.powers (single m (1 : R)))
      (coneDivisorSectionsRestrictOverChart h a) := by
  let P := dualSemigroup Phi.lattice sigma.val
  let Q := dualSemigroup Phi.lattice tau.val
  let e : AddMonoidAlgebra R P →+* AddMonoidAlgebra R Q :=
    mapDomainRingHom R (AddSubmonoid.inclusion (dualSemigroup_anti Phi.lattice h))
  let _ := Module.compHom (Phi.coneDivisorSections R tau a) e
  have hneg : -(m : N →+ ℤ) ∈ Q := by
    dsimp only [Q]
    rw [← htau]
    exact neg_mem_dualSemigroup_inf_ker Phi.lattice sigma.val m
  have hunit : IsUnit (e (single m 1)) := by
    let j := AddSubmonoid.inclusion (dualSemigroup_anti Phi.lattice h)
    have hj : IsUnit (Multiplicative.ofAdd (j m)) :=
      IsUnit.of_mul_eq_one (Multiplicative.ofAdd (⟨-m.val, hneg⟩ : Q)) <|
        congrArg Multiplicative.ofAdd (Subtype.ext (add_neg_cancel m.val))
    simpa [e, j] using hj.map (AddMonoidAlgebra.of R Q)
  refine ⟨?_, ?_, fun hxy ↦ ⟨1, ?_⟩⟩
  · rintro ⟨_, n, rfl⟩
    rw [Module.End.isUnit_iff]
    -- The endomorphism is the action of the image of the monomial power on the face module.
    change Function.Bijective
      (fun f : Phi.coneDivisorSections R tau a ↦ e (single m 1 ^ n) • f)
    rw [map_pow]
    exact (hunit.pow n).smul_bijective
  · intro f
    obtain ⟨n, hn⟩ := exists_pow_mul_mem_coneDivisorSections m.property htau f
    refine ⟨⟨⟨_, hn⟩, ⟨_, ⟨n, rfl⟩⟩⟩, Subtype.ext ?_⟩
    -- Compute the scalar action using the face ring and then its inclusion into characters.
    change (e (single m 1 ^ n) • f).val = _
    rw [AddSubmonoid.coe_smul_supportedModule]
    simp [e, mapDomainRingHom_apply]
  · have := congrArg Subtype.val hxy
    simpa only [one_smul, coe_coneDivisorSectionsRestrictOverChart, Subtype.val_inj] using this

end TauCeti.Toric.Fan

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.RepresentationTheory.Character
public import Mathlib.RepresentationTheory.Intertwining
public import Mathlib.Data.Finsupp.SMul
public import Mathlib.RingTheory.Flat.Basic
public import TauCeti.LinearAlgebra.TensorProduct.Basis
public import TauCeti.LinearAlgebra.TensorProduct.Hom
public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
public import TauCeti.RepresentationTheory.PermutationModule
-- Non-public: flat base change of kernels (`LinearMap.tensorKerEquiv`) and of finite products
-- (`TensorProduct.piRight`) are used only to construct the invariant and intertwiner comparisons.
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.LinearAlgebra.TensorProduct.Pi
-- Non-public: the bundling lemmas `FDRep.character_of` and `FDRep.character_ρ` are used only inside
-- the proof of `FDRep.character_baseChange`.
import TauCeti.RepresentationTheory.FDRep

/-!
# Base change of representations

This file extends a representation's scalars to a possibly noncommutative algebra by base-changing
each linear endomorphism. A nonzero common fixed vector after scalar extension to a base-field
algebra descends to a nonzero common fixed vector over the base field.

Two invariants survive the extension unchanged. The **character** is the trace of a linear map, and
the trace of a base-changed endomorphism is the image of the trace
(`LinearMap.trace_baseChange`), so the character of `L ⊗[K] V` is the character of `V` read in `L`.
The **intertwiner space** between two representations of a finite monoid commutes with flat scalar
extension of commutative rings when the source is finite free. An intertwiner is a linear map killed
by the finite family of conditions `σ g ∘ₗ f = f ∘ₗ ρ g`, so its space is a kernel, and flat
extension commutes with that kernel (`LinearMap.tensorKerEquiv`). Over a base field, extension
to any nontrivial commutative algebra preserves its dimension; in particular an endomorphism space
of dimension one retains that dimension.

For a finite group, the whole invariant submodule also commutes with a flat scalar extension.
Indeed, invariants are the kernel of the finite family of maps `ρ(g) - 1`; flatness preserves that
kernel, and the finite product comparison identifies the base-changed family with the invariance
conditions after extending scalars.

**Permutation representations are preserved outright.** A `G`-set `X` gives the free module
`R[X]` with `G` permuting its basis, and extending the scalars along `R → A` gives `A[X]` with the
same permutation: both sides are free on the basis `X`, and the identification matches the basis
vectors, which the two actions permute in the same way. The permutation module also occurs in the
unbundled form `X →₀ R` with the `DistribMulAction` that pushes the support forward
(`Finsupp.comapDistribMulAction`); that form is the same representation read on coefficients
(`TauCeti.ofDistribMulActionComapEquiv`, in `TauCeti.RepresentationTheory.PermutationModule`), so
its scalar extension is a permutation representation too. Over `R = ℤ` this says that the reduction
of a permutation lattice `ℤ[X]` modulo a prime is `k[X]` and its rationalization is `ℚ[X]`.

## Main declarations

* `Representation.baseChange`: scalar extension of a representation.
* `Representation.invariantsBaseChangeEquiv`: flat scalar extension commutes with taking the
  invariants of a finite group.
* `Representation.exists_common_fixed_vector_of_baseChange`: descent of a nonzero common
  fixed vector.
* `Representation.character_baseChange`: the character of a base-changed representation is the
  image of the character.
* `FDRep.character_baseChange`: the same for the scalar extension of an object of `FDRep`.
* `TauCeti.ClassFunction.ofFDRep_baseChange`: the same as class functions, the coefficients changed
  along `algebraMap K L`.
* `Representation.intertwiningMapBaseChangeEquiv`: flat scalar extension of commutative rings
  commutes with intertwiner spaces for finite monoids and finite free source modules.
* `Representation.finrank_intertwiningMap_baseChange`: scalar extension to a nontrivial
  commutative base-field algebra preserves the dimension of an intertwiner space.
* `Representation.IntertwiningMap.baseChange`: base change transports an intertwining map.
* `Representation.Equiv.baseChange`: base change transports an equivalence of representations.
* `TauCeti.baseChangeOfMulActionEquiv`: the base change of `R[X]` is `A[X]`.
* `TauCeti.baseChangeComapEquiv`: the base change of the permutation module `X →₀ R` is `A[X]`.
-/

public section

namespace TauCeti.Representation

open TensorProduct

universe u v w x

noncomputable section

variable {G : Type w} {V : Type x} [Monoid G]

section BaseChange

variable {R : Type u} {A : Type v} [CommSemiring R] [Semiring A] [Algebra R A]
variable [AddCommMonoid V] [Module R V]

/-- Extend the scalars of a representation by base-changing each linear endomorphism. -/
def _root_.Representation.baseChange (A : Type v) [Semiring A] [Algebra R A]
    (ρ : _root_.Representation R G V) : _root_.Representation A G (A ⊗[R] V) :=
  ((Module.End.baseChangeHom R A V :
      Module.End R V →ₐ[R] Module.End A (A ⊗[R] V)) :
    Module.End R V →* Module.End A (A ⊗[R] V)).comp ρ

/-- The action of a base-changed representation is the base change of the original action. -/
@[simp]
theorem _root_.Representation.baseChange_apply (ρ : _root_.Representation R G V) (g : G) :
    _root_.Representation.baseChange A ρ g = (ρ g).baseChange A :=
  by
    rw [_root_.Representation.baseChange, MonoidHom.comp_apply]
    rfl

end BaseChange

section Invariants

variable {G : Type w} [Group G]
variable {R : Type u} {A : Type v} [CommRing R] [CommRing A] [Algebra R A]
variable [Module.Flat R A] [AddCommGroup V] [Module R V]

/-- The simultaneous defect of invariance: its `g`-coordinate sends `x` to `ρ(g)x - x`.
Its kernel is the invariant submodule. -/
private def _root_.Representation.invariantDefect (ρ : _root_.Representation R G V) :
    V →ₗ[R] (G → V) :=
  LinearMap.pi fun g ↦ ρ g - LinearMap.id

private theorem _root_.Representation.mem_ker_invariantDefect
    {ρ : _root_.Representation R G V} {x : V} :
    x ∈ LinearMap.ker ρ.invariantDefect ↔ x ∈ ρ.invariants := by
  rw [LinearMap.mem_ker, funext_iff]
  simp [_root_.Representation.invariantDefect, _root_.Representation.mem_invariants, sub_eq_zero]

/-- The invariants of a representation are its simultaneous invariance kernel. -/
private def _root_.Representation.invariantsEquivKerInvariantDefect
    (ρ : _root_.Representation R G V) :
    ρ.invariants ≃ₗ[R] LinearMap.ker ρ.invariantDefect where
  toFun x := ⟨x, _root_.Representation.mem_ker_invariantDefect.mpr x.property⟩
  invFun x := ⟨x, _root_.Representation.mem_ker_invariantDefect.mp x.property⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

@[simp]
private theorem _root_.Representation.coe_invariantsEquivKerInvariantDefect
    (ρ : _root_.Representation R G V) (x : ρ.invariants) :
    (ρ.invariantsEquivKerInvariantDefect x : V) = x :=
  rfl

@[simp]
private theorem _root_.Representation.coe_invariantsEquivKerInvariantDefect_symm
    (ρ : _root_.Representation R G V) (x : LinearMap.ker ρ.invariantDefect) :
    (ρ.invariantsEquivKerInvariantDefect.symm x : V) = x :=
  rfl

omit [Module.Flat R A] in
private theorem _root_.Representation.ker_invariantDefect_baseChange [Finite G]
    (ρ : _root_.Representation R G V) :
    LinearMap.ker ((_root_.Representation.baseChange A ρ).invariantDefect) =
      LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor A A ρ.invariantDefect) := by
  classical
  let _ := Fintype.ofFinite G
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  have hDefect :
      (_root_.Representation.baseChange A ρ).invariantDefect x =
        TensorProduct.piRight R A A (fun _ : G ↦ V)
          (TensorProduct.AlgebraTensorModule.lTensor A A ρ.invariantDefect x) := by
    induction x with
    | add x y hx hy => simp [hx, hy]
    | tmul a x =>
        ext g
        simp only [_root_.Representation.invariantDefect, LinearMap.pi_apply, LinearMap.sub_apply,
          LinearMap.id_apply, LinearMap.add_apply, LinearMap.neg_apply,
          _root_.Representation.baseChange_apply,
          LinearMap.baseChange_tmul, TensorProduct.AlgebraTensorModule.lTensor_tmul,
          TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, sub_eq_add_neg]
        rw [TensorProduct.tmul_add, TensorProduct.tmul_neg]
  rw [hDefect]
  exact (TensorProduct.piRight R A A (fun _ : G ↦ V)).map_eq_zero_iff

/-- **Flat scalar extension commutes with finite-group invariants.** If `A` is flat over `R` and
`G` is finite, the scalar extension of the invariant submodule of `ρ` is naturally linearly
equivalent to the invariants of the scalar-extended representation.

Finiteness of `G` is used only to identify the scalar extension of `G → V` with
`G → A ⊗[R] V`; flatness then makes scalar extension commute with the resulting kernel. -/
noncomputable def _root_.Representation.invariantsBaseChangeEquiv [Finite G]
    (ρ : _root_.Representation R G V) :
    A ⊗[R] ρ.invariants ≃ₗ[A] (_root_.Representation.baseChange A ρ).invariants := by
  classical
  let eKer :
      LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor A A ρ.invariantDefect) ≃ₗ[A]
        LinearMap.ker ((_root_.Representation.baseChange A ρ).invariantDefect) :=
    LinearEquiv.ofEq _ _ ρ.ker_invariantDefect_baseChange.symm
  exact (AlgebraTensorModule.congr (LinearEquiv.refl A A)
      ρ.invariantsEquivKerInvariantDefect).trans <|
    (LinearMap.tensorKerEquiv A A ρ.invariantDefect).trans <|
      eKer.trans (_root_.Representation.baseChange A ρ).invariantsEquivKerInvariantDefect.symm

/-- The base-change equivalence is the canonical scalar extension of the inclusion of the
invariant submodule into the ambient representation. -/
@[simp]
theorem _root_.Representation.coe_invariantsBaseChangeEquiv [Finite G]
    (ρ : _root_.Representation R G V) (x : A ⊗[R] ρ.invariants) :
    ((ρ.invariantsBaseChangeEquiv (A := A) x :
        (_root_.Representation.baseChange A ρ).invariants) : A ⊗[R] V) =
      ρ.invariants.subtype.lTensor A x := by
  classical
  induction x with
  | add x y hx hy => simpa only [map_add, Submodule.coe_add] using congrArg₂ (· + ·) hx hy
  | tmul a x =>
      simp only [_root_.Representation.invariantsBaseChangeEquiv, LinearEquiv.trans_apply,
        AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
        _root_.Representation.coe_invariantsEquivKerInvariantDefect_symm,
        LinearEquiv.coe_ofEq_apply, LinearMap.tensorKerEquiv_apply, LinearMap.tensorKer_tmul,
        _root_.Representation.coe_invariantsEquivKerInvariantDefect, LinearMap.lTensor_tmul,
        Submodule.subtype_apply]

end Invariants

variable {K : Type u} {L : Type v} [Field K] [Semiring L] [Algebra K L]
variable [AddCommGroup V] [Module K V]

/-- A nonzero common fixed vector after scalar extension to a base-field algebra descends to a
nonzero common fixed vector over the base field. Neither commutativity nor nontriviality of the
coefficient algebra is needed. -/
theorem _root_.Representation.exists_common_fixed_vector_of_baseChange
    (ρ : _root_.Representation K G V) {w : L ⊗[K] V} (hw : w ≠ 0)
    (hfixed : ∀ g, _root_.Representation.baseChange L ρ g w = w) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  classical
  -- A module over the base field has its canonical additive group structure, even when the
  -- coefficient algebra is presented as a semiring.
  let : AddCommGroup L := Module.addCommMonoidToAddCommGroup K
  let b := Module.Free.chooseBasis K L
  let e := TensorProduct.equivFinsuppOfBasisLeft b (N := V)
  have he : e w ≠ 0 := fun h ↦ hw (e.map_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp he
  simp only [Finsupp.coe_zero, Pi.zero_apply] at hi
  refine ⟨e w i, hi, fun g ↦ ?_⟩
  rw [← Module.Basis.equivFinsuppOfBasisLeft_lTensor_apply]
  exact congrArg (fun x ↦ e x i) (hfixed g)

end

section Character

open TensorProduct

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
variable {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]

/-- **The character is unchanged by base change**, read through the structure map: the character of
`L ⊗[K] V` at `g` is the image in `L` of the character of `V` at `g`, because the trace of a
base-changed endomorphism is the image of its trace. -/
@[simp]
theorem _root_.Representation.character_baseChange {G : Type*} [Monoid G]
    (ρ : _root_.Representation K G V) (g : G) :
    (_root_.Representation.baseChange L ρ).character g = algebraMap K L (ρ.character g) := by
  simp [_root_.Representation.character, _root_.Representation.baseChange_apply,
    LinearMap.trace_baseChange]

/-- **The character of a scalar extension in `FDRep`** is the character of the original
representation read in the larger field: `χ_{L ⊗[K] V} = algebraMap K L ∘ χ_V`.

Not `@[simp]`: its left-hand side is not in simp normal form, since `simp` already rewrites it
with `FDRep.character_of` and then the pointwise `Representation.character_baseChange`. -/
theorem _root_.FDRep.character_baseChange {K L : Type u} [Field K] [Field L] [Algebra K L]
    {G : Type*} [Monoid G] (V : FDRep K G) :
    (FDRep.of (_root_.Representation.baseChange L V.ρ)).character =
      algebraMap K L ∘ V.character := by
  funext g
  rw [FDRep.character_of, _root_.Representation.character_baseChange, Function.comp_apply,
    FDRep.character_ρ]

/-- **The class function of a scalar extension in `FDRep`** is the class function of the original
representation with its coefficients changed along `algebraMap K L`. -/
@[simp]
theorem _root_.TauCeti.ClassFunction.ofFDRep_baseChange {K L : Type u} [Field K] [Field L]
    [Algebra K L] {G : Type*} [Group G] (V : FDRep K G) :
    ClassFunction.ofFDRep (FDRep.of (_root_.Representation.baseChange L V.ρ)) =
      ClassFunction.map (algebraMap K L) (ClassFunction.ofFDRep V) :=
  Subtype.ext (funext fun g => by
    rw [ClassFunction.ofFDRep_apply, ClassFunction.map_apply, ClassFunction.ofFDRep_apply,
      FDRep.character_baseChange, Function.comp_apply])

end Character

end TauCeti.Representation

-- The intertwiner argument is staged through private helpers taking explicit `Representation`
-- arguments. A Mathlib namespace nested under `TauCeti` gives no dot notation on the Mathlib type,
-- so those helpers sit directly under `TauCeti` rather than under `TauCeti.Representation`.
namespace TauCeti

section Transport

open TensorProduct

variable {R : Type*} [CommSemiring R] {G : Type*} [Monoid G]
  {V W : Type*} [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  {ρ : _root_.Representation R G V} {σ : _root_.Representation R G W}

/-- **Base change transports an intertwining map**: `A ⊗ f : A ⊗[R] V → A ⊗[R] W` intertwines the
base-changed representations, because the extension acts on the second factor, where `f` already
intertwines the two actions. -/
def _root_.Representation.IntertwiningMap.baseChange
    (f : _root_.Representation.IntertwiningMap ρ σ) (A : Type*) [Semiring A] [Algebra R A] :
    _root_.Representation.IntertwiningMap (_root_.Representation.baseChange A ρ)
      (_root_.Representation.baseChange A σ) where
  toLinearMap := f.toLinearMap.baseChange A
  isIntertwining' g := by
    ext a
    simp [f.isIntertwining]

/-- A base-changed intertwining map acts on the second factor of a pure tensor. -/
@[simp]
theorem _root_.Representation.IntertwiningMap.baseChange_tmul
    (f : _root_.Representation.IntertwiningMap ρ σ) (A : Type*) [Semiring A] [Algebra R A]
    (a : A) (v : V) : f.baseChange A (a ⊗ₜ[R] v) = a ⊗ₜ[R] f v :=
  (rfl)

/-- The linear map underlying a base-changed intertwining map is the base change of the
underlying linear map. -/
@[simp]
theorem _root_.Representation.IntertwiningMap.toLinearMap_baseChange
    (f : _root_.Representation.IntertwiningMap ρ σ) (A : Type*) [Semiring A] [Algebra R A] :
    (f.baseChange A).toLinearMap = f.toLinearMap.baseChange A :=
  (rfl)

/-- **Base change preserves composition**: the base change of `g ∘ f` is the composite of the base
changes `A ⊗ g ∘ A ⊗ f`. -/
@[simp]
theorem _root_.Representation.IntertwiningMap.baseChange_comp {U : Type*} [AddCommMonoid U]
    [Module R U] {τ : _root_.Representation R G U}
    (g : _root_.Representation.IntertwiningMap σ τ) (f : _root_.Representation.IntertwiningMap ρ σ)
    (A : Type*) [Semiring A] [Algebra R A] :
    (g.comp f).baseChange A = (g.baseChange A).comp (f.baseChange A) :=
  _root_.Representation.IntertwiningMap.ext (LinearMap.baseChange_comp ..)

/-- **Base change preserves a scalar composite**: if `g ∘ f` is multiplication by `r : R`, then so
is the composite of the base changes `A ⊗ g ∘ A ⊗ f`. -/
theorem _root_.Representation.IntertwiningMap.baseChange_apply_baseChange_apply_of_comp_eq_smul
    {f : _root_.Representation.IntertwiningMap ρ σ} {g : _root_.Representation.IntertwiningMap σ ρ}
    {r : R} (hgf : ∀ v, g (f v) = r • v) (A : Type*) [Semiring A] [Algebra R A]
    (x : A ⊗[R] V) : g.baseChange A (f.baseChange A x) = r • x := by
  have hcomp : g.toLinearMap ∘ₗ f.toLinearMap = r • LinearMap.id := LinearMap.ext hgf
  have h := congrArg (fun φ ↦ φ.toLinearMap)
    (_root_.Representation.IntertwiningMap.baseChange_comp g f A)
  rw [_root_.Representation.IntertwiningMap.toLinearMap_baseChange,
    _root_.Representation.IntertwiningMap.comp_toLinearMap, hcomp,
    LinearMap.baseChange_smul, LinearMap.baseChange_id] at h
  exact (LinearMap.congr_fun h x).symm

/-- An intertwining map with two scalar inverse composites becomes bijective after base
change whenever both scalars become units in the new coefficient semiring. -/
theorem _root_.Representation.IntertwiningMap.baseChange_bijective_of_comp_eq_smul
    {f : _root_.Representation.IntertwiningMap ρ σ} {g : _root_.Representation.IntertwiningMap σ ρ}
    {r s : R} (hgf : ∀ v, g (f v) = r • v) (hfg : ∀ w, f (g w) = s • w)
    (A : Type*) [Semiring A] [Algebra R A] (hr : IsUnit (algebraMap R A r))
    (hs : IsUnit (algebraMap R A s)) :
    Function.Bijective (f.baseChange A) := by
  have hgfA (x : A ⊗[R] V) :
      g.baseChange A (f.baseChange A x) = algebraMap R A r • x := by
    simpa only [IsScalarTower.algebraMap_smul] using
      _root_.Representation.IntertwiningMap.baseChange_apply_baseChange_apply_of_comp_eq_smul
        hgf A x
  have hfgA (y : A ⊗[R] W) :
      f.baseChange A (g.baseChange A y) = algebraMap R A s • y := by
    simpa only [IsScalarTower.algebraMap_smul] using
      _root_.Representation.IntertwiningMap.baseChange_apply_baseChange_apply_of_comp_eq_smul
        hfg A y
  refine ⟨fun x y hxy ↦ hr.smul_left_cancel.mp ?_,
    fun y ↦ ⟨g.baseChange A (hs.unit⁻¹ • y), ?_⟩⟩
  · rw [← hgfA, ← hgfA, hxy]
  · rw [hfgA]
    exact smul_inv_smul hs.unit y

/-- **Base change transports an equivalence of representations**: an equivariant isomorphism
`ρ ≃ σ` becomes an equivariant isomorphism `A ⊗[R] V ≃ A ⊗[R] W` after extending the scalars,
because the extension acts on the second factor, where the equivalence already intertwines the
two actions. -/
def _root_.Representation.Equiv.baseChange (φ : ρ.Equiv σ) (A : Type*) [Semiring A]
    [Algebra R A] :
    (_root_.Representation.baseChange A ρ).Equiv (_root_.Representation.baseChange A σ) :=
  _root_.Representation.Equiv.mk
    (AlgebraTensorModule.congr (LinearEquiv.refl A A) φ.toLinearEquiv) fun g => by
      ext a
      simp [φ.toIntertwiningMap.isIntertwining]

/-- A base-changed equivalence acts on the second factor of a pure tensor. -/
@[simp]
theorem _root_.Representation.Equiv.baseChange_tmul (φ : ρ.Equiv σ) (A : Type*) [Semiring A]
    [Algebra R A] (a : A) (v : V) : φ.baseChange A (a ⊗ₜ[R] v) = a ⊗ₜ[R] φ v := by
  simp only [_root_.Representation.Equiv.baseChange, _root_.Representation.Equiv.mk_apply,
    AlgebraTensorModule.congr_tmul, LinearEquiv.refl_apply,
    _root_.Representation.Equiv.toLinearEquiv_apply,
    _root_.Representation.Equiv.coe_toIntertwiningMap]

/-- The inverse of a base-changed equivalence acts by the inverse on the second factor of a pure
tensor. -/
@[simp]
theorem _root_.Representation.Equiv.baseChange_symm_tmul (φ : ρ.Equiv σ) (A : Type*)
    [Semiring A] [Algebra R A] (a : A) (w : W) :
    (φ.baseChange A).symm (a ⊗ₜ[R] w) = a ⊗ₜ[R] φ.symm w := by
  have h : φ.baseChange A (a ⊗ₜ[R] φ.symm w) = a ⊗ₜ[R] w := by
    rw [_root_.Representation.Equiv.baseChange_tmul,
      _root_.Representation.Equiv.apply_symm_apply]
  rw [← h, _root_.Representation.Equiv.symm_apply_apply]

end Transport

section Intertwiner

open TensorProduct

variable {K : Type*} {L : Type*} [CommRing K] [CommRing L] [Algebra K L]
variable {G : Type*} [Monoid G]
variable {V : Type*} [AddCommGroup V] [Module K V]
variable {W : Type*} [AddCommGroup W] [Module K W]

/-- The **intertwining defect** of a linear map `f : V →ₗ[K] W`: the family
`g ↦ σ g ∘ₗ f - f ∘ₗ ρ g`, whose vanishing is exactly the intertwining condition. Writing the
intertwiner space as the kernel of a single linear map is what makes it visibly compatible with
base change, `L` being flat over `K`. -/
private def intertwiningDefect (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W) :
    (V →ₗ[K] W) →ₗ[K] (G → (V →ₗ[K] W)) :=
  LinearMap.pi fun g => LinearMap.llcomp K V W W (σ g) - LinearMap.lcomp K W (ρ g)

private theorem intertwiningDefect_apply (ρ : _root_.Representation K G V)
    (σ : _root_.Representation K G W) (f : V →ₗ[K] W) (g : G) :
    intertwiningDefect ρ σ f g = σ g ∘ₗ f - f ∘ₗ ρ g :=
  rfl

private theorem mem_ker_intertwiningDefect {ρ : _root_.Representation K G V}
    {σ : _root_.Representation K G W} {f : V →ₗ[K] W} :
    f ∈ LinearMap.ker (intertwiningDefect ρ σ) ↔ ∀ g, f ∘ₗ ρ g = σ g ∘ₗ f := by
  rw [LinearMap.mem_ker, funext_iff]
  refine forall_congr' fun g => ?_
  rw [intertwiningDefect_apply, Pi.zero_apply, sub_eq_zero, eq_comm]

/-- The intertwiner space is the kernel of the intertwining defect. -/
private def intertwiningMapEquivKerDefect (ρ : _root_.Representation K G V)
    (σ : _root_.Representation K G W) :
    _root_.Representation.IntertwiningMap ρ σ ≃ₗ[K] LinearMap.ker (intertwiningDefect ρ σ) where
  toFun f := ⟨f.toLinearMap, mem_ker_intertwiningDefect.mpr f.isIntertwining'⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f.1, mem_ker_intertwiningDefect.mp f.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The intertwining defect of a base-changed map is the base change of its defect**,
componentwise: base change is compatible with composition and subtraction, and the base-changed
representations act by the base-changed operators. -/
private theorem intertwiningDefect_baseChange (ρ : _root_.Representation K G V)
    (σ : _root_.Representation K G W) (f : V →ₗ[K] W) (g : G) :
    intertwiningDefect (_root_.Representation.baseChange L ρ)
        (_root_.Representation.baseChange L σ) (f.baseChange L) g
      = (intertwiningDefect ρ σ f g).baseChange L := by
  rw [intertwiningDefect_apply, intertwiningDefect_apply, LinearMap.baseChange_sub,
    LinearMap.baseChange_comp, LinearMap.baseChange_comp, _root_.Representation.baseChange_apply,
    _root_.Representation.baseChange_apply]

variable [Module.Free K V] [Module.Finite K V]

/-- The intertwining defect commutes with scalar extension. -/
private theorem intertwiningDefect_homBaseChangeEquiv [Fintype G] [DecidableEq G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W)
    (x : L ⊗[K] (V →ₗ[K] W)) :
    intertwiningDefect (_root_.Representation.baseChange L ρ)
        (_root_.Representation.baseChange L σ)
        ((LinearMap.isBaseChange_baseChangeHom K L V W).equiv x)
      = ((TensorProduct.piRight K L L _).trans
          (LinearEquiv.piCongrRight fun _ ↦ (LinearMap.isBaseChange_baseChangeHom K L V W).equiv))
          (TensorProduct.AlgebraTensorModule.lTensor L L (intertwiningDefect ρ σ) x) := by
  induction x with
  | add x y hx hy => simp [hx, hy]
  | tmul a f =>
    funext g
    -- the defect is linear, so both sides are `a • (intertwiningDefect ρ σ f g)`
    -- base-changed to `L`
    simp only [IsBaseChange.equiv_tmul, LinearMap.baseChangeHom_apply, _root_.map_smul,
      Pi.smul_apply, intertwiningDefect_baseChange,
      TensorProduct.AlgebraTensorModule.lTensor_tmul, LinearEquiv.trans_apply,
      LinearEquiv.piCongrRight_apply, TensorProduct.piRight_apply,
      TensorProduct.piRightHom_tmul]

/-- Pulling back the base-changed intertwining kernel along scalar extension of linear maps gives
the kernel of the scalar-extended defect. -/
private theorem comap_ker_intertwiningDefect_baseChange [Finite G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W) :
    Submodule.comap ((LinearMap.isBaseChange_baseChangeHom K L V W).equiv :
        L ⊗[K] (V →ₗ[K] W) →ₗ[L] _)
        (LinearMap.ker (intertwiningDefect (_root_.Representation.baseChange L ρ)
          (_root_.Representation.baseChange L σ)))
      = LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor L L
          (intertwiningDefect ρ σ)) := by
  classical
  let _ := Fintype.ofFinite G
  ext x
  rw [Submodule.mem_comap, LinearMap.mem_ker, LinearMap.mem_ker, LinearEquiv.coe_coe,
    intertwiningDefect_homBaseChangeEquiv]
  exact ((TensorProduct.piRight K L L (fun _ : G ↦ V →ₗ[K] W)).trans
    (LinearEquiv.piCongrRight fun _ : G ↦
      (LinearMap.isBaseChange_baseChangeHom K L V W).equiv)).map_eq_zero_iff

/-- Flat scalar extension commutes with the intertwiner space for a finite monoid and a finite
free source module. On pure tensors this is scalar multiplication of the base-changed
intertwining map (`Representation.intertwiningMapBaseChangeEquiv_tmul`). -/
noncomputable def _root_.Representation.intertwiningMapBaseChangeEquiv
    [Module.Flat K L] [Finite G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W) :
    L ⊗[K] _root_.Representation.IntertwiningMap ρ σ ≃ₗ[L]
      _root_.Representation.IntertwiningMap (_root_.Representation.baseChange L ρ)
        (_root_.Representation.baseChange L σ) :=
  (AlgebraTensorModule.congr (LinearEquiv.refl L L)
      (intertwiningMapEquivKerDefect ρ σ)).trans <|
    (LinearMap.tensorKerEquiv L L (intertwiningDefect ρ σ)).trans <|
      (LinearEquiv.ofEq _ _ (comap_ker_intertwiningDefect_baseChange ρ σ).symm).trans <|
        (LinearEquiv.ofSubmodule' (LinearMap.isBaseChange_baseChangeHom K L V W).equiv _).trans
          (intertwiningMapEquivKerDefect (_root_.Representation.baseChange L ρ)
            (_root_.Representation.baseChange L σ)).symm

/-- Scalar extension of the intertwiner space sends a pure tensor to the corresponding scalar
multiple of the base-changed intertwining map. -/
@[simp]
theorem _root_.Representation.intertwiningMapBaseChangeEquiv_tmul
    [Module.Flat K L] [Finite G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W)
    (a : L) (f : _root_.Representation.IntertwiningMap ρ σ) :
    ρ.intertwiningMapBaseChangeEquiv σ (a ⊗ₜ[K] f) = a • f.baseChange L := by
  ext v
  simp [_root_.Representation.intertwiningMapBaseChangeEquiv,
    intertwiningMapEquivKerDefect, IsBaseChange.equiv_tmul]

/-- The inverse comparison sends a base-changed intertwining map to its canonical pure tensor. -/
@[simp]
theorem _root_.Representation.intertwiningMapBaseChangeEquiv_symm_baseChange
    [Module.Flat K L] [Finite G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W)
    (f : _root_.Representation.IntertwiningMap ρ σ) :
    (ρ.intertwiningMapBaseChangeEquiv σ).symm (f.baseChange L) = 1 ⊗ₜ[K] f := by
  rw [LinearEquiv.symm_apply_eq, _root_.Representation.intertwiningMapBaseChangeEquiv_tmul,
    one_smul]

end Intertwiner

section IntertwinerDimension

open TensorProduct

variable {K L G V W : Type*} [Field K] [CommRing L] [Nontrivial L] [Algebra K L]
  [Monoid G] [Finite G] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  [AddCommGroup W] [Module K W]

/-- Scalar extension to a nontrivial commutative algebra preserves the dimension of an intertwiner
space for a finite monoid and a finite-dimensional source representation. Over the coefficient
algebra the extended intertwiner space is free, with the same rank as the original vector space. -/
theorem _root_.Representation.finrank_intertwiningMap_baseChange
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W) :
    Module.finrank L (_root_.Representation.IntertwiningMap
        (_root_.Representation.baseChange L ρ) (_root_.Representation.baseChange L σ))
      = Module.finrank K (_root_.Representation.IntertwiningMap ρ σ) := by
  rw [← (ρ.intertwiningMapBaseChangeEquiv σ).finrank_eq, Module.finrank_baseChange]

end IntertwinerDimension

section PermutationRepresentation

open TensorProduct

section PermutationModule

variable (R : Type*) [CommSemiring R] (A : Type*) [Semiring A] [Algebra R A]
  (G : Type*) [Monoid G] (X : Type*) [MulAction G X]

/-- **The base change of a permutation representation is the permutation representation over the
target ring**: extending the scalars of `R[X]` along the structure map `R → A` of an
`R`-algebra `A` gives `A[X]`, equivariantly for a monoid acting on `X`. Nothing is asked of that
structure map — `A` need not contain `R` — beyond its being an `R`-algebra. Both sides are free on
the basis `X` and the identification matches those basis vectors, which the two actions permute in
the same way. -/
noncomputable def baseChangeOfMulActionEquiv :
    (_root_.Representation.baseChange A (_root_.Representation.ofMulAction R G X)).Equiv
      (_root_.Representation.ofMulAction A G X) :=
  _root_.Representation.Equiv.mk
    (((MonoidAlgebra.basis X R).baseChange A).equiv (MonoidAlgebra.basis X A) (Equiv.refl X))
    fun g => by
      have h (x : X) :
          ((MonoidAlgebra.basis X R).baseChange A).equiv (MonoidAlgebra.basis X A)
              (Equiv.refl X) (1 ⊗ₜ[R] MonoidAlgebra.single x 1) = MonoidAlgebra.single x 1 := by
        simpa only [Module.Basis.baseChange_apply, MonoidAlgebra.basis_apply, Equiv.refl_apply]
          using (((MonoidAlgebra.basis X R).baseChange A).equiv_apply x
            (MonoidAlgebra.basis X A) (Equiv.refl X))
      apply ((MonoidAlgebra.basis X R).baseChange A).ext
      intro x
      simp [Module.Basis.baseChange_apply, h]

variable {R A X}

/-- `TauCeti.baseChangeOfMulActionEquiv` on the pure tensors spanning the scalar extension. -/
@[simp]
theorem baseChangeOfMulActionEquiv_tmul_single (a : A) (x : X) (r : R) :
    baseChangeOfMulActionEquiv R A G X (a ⊗ₜ[R] MonoidAlgebra.single x r)
      = MonoidAlgebra.single x (r • a) := by
  have h : baseChangeOfMulActionEquiv R A G X (1 ⊗ₜ[R] MonoidAlgebra.single x 1) =
      MonoidAlgebra.single x 1 := by
    simpa only [baseChangeOfMulActionEquiv, _root_.Representation.Equiv.mk_apply,
      Module.Basis.baseChange_apply, MonoidAlgebra.basis_apply, Equiv.refl_apply]
      using (((MonoidAlgebra.basis X R).baseChange A).equiv_apply x
        (MonoidAlgebra.basis X A) (Equiv.refl X))
  have ht : a ⊗ₜ[R] MonoidAlgebra.single x r =
      (r • a) • (1 ⊗ₜ[R] MonoidAlgebra.single x 1) := by
    simp only [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [TensorProduct.smul_tmul]
    simp only [MonoidAlgebra.smul_single', mul_one]
  rw [ht, map_smul, h]
  simp only [MonoidAlgebra.smul_single', mul_one]

/-- `TauCeti.baseChangeOfMulActionEquiv` carries the element of `A[X]` supported at `x` with
coefficient `a` back to the pure tensor `a ⊗ₜ single x 1`; at `a = 1` this matches the two bases. -/
@[simp]
theorem baseChangeOfMulActionEquiv_symm_single (a : A) (x : X) :
    (baseChangeOfMulActionEquiv R A G X).symm (MonoidAlgebra.single x a)
      = a ⊗ₜ[R] MonoidAlgebra.single x 1 := by
  have h : baseChangeOfMulActionEquiv R A G X (a ⊗ₜ[R] MonoidAlgebra.single x 1)
      = MonoidAlgebra.single x a := by
    rw [baseChangeOfMulActionEquiv_tmul_single, one_smul]
  rw [← h, _root_.Representation.Equiv.symm_apply_apply]

end PermutationModule

section Comap

attribute [local instance] Finsupp.comapSMul Finsupp.comapMulAction Finsupp.comapDistribMulAction
  comapSMulCommClass

variable (R : Type*) [CommSemiring R] (A : Type*) [Semiring A] [Algebra R A]
  (G : Type*) [Monoid G] (X : Type*) [MulAction G X]

/-- **The base change of a permutation module is a permutation representation.** At `R = ℤ` this
says that extending the scalars of the permutation lattice `ℤ[X] = X →₀ ℤ` along `ℤ → A` gives the
permutation representation `A[X]`: the reduction of `ℤ[X]` modulo a prime is `k[X]`, and its
rationalization is `ℚ[X]`. It is `TauCeti.ofDistribMulActionComapEquiv` base-changed along
`Representation.Equiv.baseChange` and followed by `TauCeti.baseChangeOfMulActionEquiv`. -/
noncomputable def baseChangeComapEquiv :
    (_root_.Representation.baseChange A
        (_root_.Representation.ofDistribMulAction R G (X →₀ R))).Equiv
      (_root_.Representation.ofMulAction A G X) :=
  ((ofDistribMulActionComapEquiv R G X).baseChange A).trans (baseChangeOfMulActionEquiv R A G X)

variable {R A X}

/-- `TauCeti.baseChangeComapEquiv` on the pure tensors spanning the scalar extension. -/
@[simp]
theorem baseChangeComapEquiv_tmul_single (a : A) (x : X) (r : R) :
    baseChangeComapEquiv R A G X (a ⊗ₜ[R] Finsupp.single x r)
      = MonoidAlgebra.single x (r • a) := by
  simp only [baseChangeComapEquiv, _root_.Representation.Equiv.trans_apply,
    _root_.Representation.Equiv.baseChange_tmul, ofDistribMulActionComapEquiv_single,
    baseChangeOfMulActionEquiv_tmul_single]

/-- `TauCeti.baseChangeComapEquiv` carries the element of `A[X]` supported at `x` with coefficient
`a` back to the pure tensor `a ⊗ₜ single x 1`. -/
@[simp]
theorem baseChangeComapEquiv_symm_single (a : A) (x : X) :
    (baseChangeComapEquiv R A G X).symm (MonoidAlgebra.single x a)
      = a ⊗ₜ[R] Finsupp.single x 1 := by
  have h : baseChangeComapEquiv R A G X (a ⊗ₜ[R] Finsupp.single x 1)
      = MonoidAlgebra.single x a := by
    rw [baseChangeComapEquiv_tmul_single, one_smul]
  rw [← h, _root_.Representation.Equiv.symm_apply_apply]

end Comap

end PermutationRepresentation

end TauCeti

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
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import TauCeti.LinearAlgebra.TensorProduct.Basis
-- Non-public: the flat base change of a kernel (`LinearMap.tensorKerEquiv`), the scalar extension
-- of a space of linear maps (`IsBaseChange.linearMapLeftRight`) and of a finite product
-- (`TensorProduct.piRight`) are used only inside the proof of
-- `Representation.finrank_intertwiningMap_baseChange`.
import Mathlib.RingTheory.Flat.Equalizer
import Mathlib.RingTheory.TensorProduct.IsBaseChangeHom
import Mathlib.LinearAlgebra.TensorProduct.Pi

/-!
# Base change of representations

This file extends a representation's scalars by base-changing each linear endomorphism. It also
records the descent step needed for fixed vectors: a nonzero common fixed vector after a field
extension yields a nonzero common fixed vector over the base field.

Two invariants survive the extension unchanged. The **character** is the trace of a linear map, and
the trace of a base-changed endomorphism is the image of the trace
(`LinearMap.trace_baseChange`), so the character of `L ⊗[K] V` is the character of `V` read in `L`.
The **dimension of an intertwiner space** between two representations of a finite monoid, the
source finite-dimensional, is unchanged as well: an intertwiner is a linear map killed by the
finite family of conditions `σ g ∘ₗ f = f ∘ₗ ρ g`, so the intertwiner space is the kernel of a
single linear map, and the extension is flat, so it commutes with that kernel
(`LinearMap.tensorKerEquiv`). Applied to a representation whose endomorphism algebra is
one-dimensional, that equality says the endomorphism algebra after the extension is one-dimensional
again, which is the mechanism by which an absolutely irreducible representation stays irreducible
over any extension.

**Permutation representations are preserved outright.** A `G`-set `X` gives the free module
`R[X]` with `G` permuting its basis, and extending the scalars along `R → A` gives `A[X]` with the
same permutation: both sides are free on the basis `X`, and the identification matches the basis
vectors, which the two actions permute in the same way. The permutation module also occurs in the
unbundled form `X →₀ R` with the `DistribMulAction` that pushes the support forward
(`Finsupp.comapDistribMulAction`), and that form is the same representation read on coefficients.
Over `R = ℤ` this says that the reduction of a permutation lattice `ℤ[X]` modulo a prime is `k[X]`
and its rationalization is `ℚ[X]`.

## Main declarations

* `Representation.baseChange`: scalar extension of a representation.
* `Representation.exists_common_fixed_vector_of_baseChange`: descent of a nonzero common
  fixed vector.
* `Representation.character_baseChange`: the character of a base-changed representation is the
  image of the character.
* `Representation.finrank_intertwiningMap_baseChange`: base change preserves the dimension of an
  intertwiner space.
* `Representation.Equiv.baseChange`: base change transports an equivalence of representations.
* `TauCeti.baseChangeOfMulActionEquiv`: the base change of `R[X]` is `A[X]`.
* `TauCeti.ofDistribMulActionComapEquiv`: the unbundled permutation module `X →₀ R` is the
  permutation representation `R[X]`.
* `TauCeti.baseChangeComapEquiv`: the base change of the permutation module `X →₀ R` is `A[X]`.
-/

public section

namespace TauCeti.Representation

open TensorProduct

universe u v w x

noncomputable section

variable {G : Type w} {V : Type x} [Monoid G]

section BaseChange

variable {R : Type u} {A : Type v} [CommSemiring R] [CommSemiring A] [Algebra R A]
variable [AddCommMonoid V] [Module R V]

/-- Extend the scalars of a representation by base-changing each linear endomorphism. -/
def _root_.Representation.baseChange (A : Type v) [CommSemiring A] [Algebra R A]
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

variable {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
variable [AddCommGroup V] [Module K V]

/-- A nonzero common fixed vector after a field extension descends to a nonzero common fixed
vector over the base field. -/
theorem _root_.Representation.exists_common_fixed_vector_of_baseChange
    (ρ : _root_.Representation K G V) {w : L ⊗[K] V} (hw : w ≠ 0)
    (hfixed : ∀ g, _root_.Representation.baseChange L ρ g w = w) :
    ∃ v : V, v ≠ 0 ∧ ∀ g, ρ g v = v := by
  let b := Module.Free.chooseBasis K V
  have hwrepr : (b.baseChange L).repr w ≠ 0 := fun h ↦
    hw ((b.baseChange L).repr.map_eq_zero_iff.mp h)
  obtain ⟨i, hi⟩ := Finsupp.ne_iff.mp hwrepr
  rw [Finsupp.coe_zero, Pi.zero_apply] at hi
  obtain ⟨phi, hphi⟩ := Module.Projective.exists_dual_ne_zero K hi
  let descend : L ⊗[K] V →ₗ[K] V :=
    (TensorProduct.lid K V).toLinearMap.comp (phi.rTensor V)
  have hbmap : (b.baseChange K).map (TensorProduct.lid K V) = b := by
    ext j
    simp
  have hbmap_repr (y : K ⊗[K] V) (j) :
      b.repr (TensorProduct.lid K V y) j = (b.baseChange K).repr y j := by
    have h := congrArg (fun c : Module.Basis _ K V ↦
      c.repr (TensorProduct.lid K V y) j) hbmap
    rw [Module.Basis.map_repr] at h
    simpa using h.symm
  have descend_repr (x : L ⊗[K] V) (j) :
      b.repr (descend x) j = phi ((b.baseChange L).repr x j) := by
    have descend_apply :
        descend x = TensorProduct.lid K V ((phi.rTensor V) x) := rfl
    calc
      b.repr (descend x) j =
          (b.baseChange K).repr ((phi.rTensor V) x) j := by
        rw [descend_apply]
        exact hbmap_repr ((phi.rTensor V) x) j
      _ = phi ((b.baseChange L).repr x j) := by
        rw [LinearMap.rTensor_def]
        exact (Module.Basis.map_baseChange_repr b phi x j).symm
  have descend_baseChange (f : Module.End K V) (x : L ⊗[K] V) :
      descend (f.baseChange L x) = f (descend x) := by
    have hcomm :
        (phi.rTensor V).comp (f.lTensor L) = (f.lTensor K).comp (phi.rTensor V) := by
      rw [LinearMap.rTensor_comp_lTensor, LinearMap.lTensor_comp_rTensor]
    have hlid :
        (TensorProduct.lid K V).toLinearMap.comp (f.lTensor K) =
          f.comp (TensorProduct.lid K V).toLinearMap := by
      ext a
      simp
    calc
      descend (f.baseChange L x) =
          TensorProduct.lid K V ((phi.rTensor V) ((f.lTensor L) x)) := by
        rw [LinearMap.baseChange_eq_ltensor]
        rfl
      _ = TensorProduct.lid K V ((f.lTensor K) ((phi.rTensor V) x)) := by
        apply congrArg (TensorProduct.lid K V)
        simpa only [LinearMap.comp_apply] using LinearMap.congr_fun hcomm x
      _ = f (TensorProduct.lid K V ((phi.rTensor V) x)) :=
        LinearMap.congr_fun hlid ((phi.rTensor V) x)
      _ = f (descend x) := rfl
  refine ⟨descend w, ?_, fun g ↦ ?_⟩
  · intro hzero
    apply hphi
    rw [← descend_repr w i, hzero]
    simp
  · rw [← descend_baseChange]
    exact congrArg descend (hfixed g)

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

end Character

end TauCeti.Representation

-- The intertwiner argument is staged through private helpers taking explicit `Representation`
-- arguments. A Mathlib namespace nested under `TauCeti` gives no dot notation on the Mathlib type,
-- so those helpers sit directly under `TauCeti` rather than under `TauCeti.Representation`.
namespace TauCeti

section Intertwiner

open TensorProduct

variable {K : Type*} {L : Type*} [Field K] [Field L] [Algebra K L]
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

variable [FiniteDimensional K V]

variable (K L V W) in
/-- Scalar extension of linear maps out of a finite-dimensional space: `L ⊗[K] (V →ₗ[K] W)` is the
space of `L`-linear maps `L ⊗[K] V →ₗ[L] L ⊗[K] W`. -/
private noncomputable def homBaseChangeEquiv :
    L ⊗[K] (V →ₗ[K] W) ≃ₗ[L] ((L ⊗[K] V) →ₗ[L] (L ⊗[K] W)) :=
  ((TensorProduct.isBaseChange K V L).linearMapLeftRight
    (TensorProduct.isBaseChange K W L)).equiv

private theorem homBaseChangeEquiv_tmul (a : L) (f : V →ₗ[K] W) :
    homBaseChangeEquiv K L V W (a ⊗ₜ f) = a • f.baseChange L := by
  rw [homBaseChangeEquiv, IsBaseChange.equiv_tmul]
  congr 1
  ext v
  exact IsBaseChange.linearMapLeftRightHom_comp_apply (TensorProduct.isBaseChange K V L)
    ((TensorProduct.mk K L W) 1) f v

variable (K L V W) in
/-- Scalar extension of a finite family of linear maps, componentwise. -/
private noncomputable def piBaseChangeEquiv (G : Type*) [Fintype G] [DecidableEq G] :
    L ⊗[K] (G → (V →ₗ[K] W)) ≃ₗ[L] (G → ((L ⊗[K] V) →ₗ[L] (L ⊗[K] W))) :=
  (TensorProduct.piRight K L L _).trans
    (LinearEquiv.piCongrRight fun _ => homBaseChangeEquiv K L V W)

private theorem piBaseChangeEquiv_tmul {G : Type*} [Fintype G] [DecidableEq G] (a : L)
    (f : G → (V →ₗ[K] W)) (g : G) :
    piBaseChangeEquiv K L V W G (a ⊗ₜ[K] f) g = a • (f g).baseChange L := by
  rw [piBaseChangeEquiv, LinearEquiv.trans_apply, LinearEquiv.piCongrRight_apply,
    TensorProduct.piRight_apply, TensorProduct.piRightHom_tmul, homBaseChangeEquiv_tmul]

/-- The intertwining defect commutes with scalar extension. -/
private theorem intertwiningDefect_homBaseChangeEquiv [Fintype G] [DecidableEq G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W)
    (x : L ⊗[K] (V →ₗ[K] W)) :
    intertwiningDefect (_root_.Representation.baseChange L ρ)
        (_root_.Representation.baseChange L σ) (homBaseChangeEquiv K L V W x)
      = piBaseChangeEquiv K L V W G
          (TensorProduct.AlgebraTensorModule.lTensor L L (intertwiningDefect ρ σ) x) := by
  induction x with
  | add x y hx hy => simp [hx, hy]
  | tmul a f =>
    funext g
    -- the defect is linear, so both sides are `a • (intertwiningDefect ρ σ f g)`
    -- base-changed to `L`
    rw [homBaseChangeEquiv_tmul, _root_.map_smul, Pi.smul_apply, intertwiningDefect_baseChange,
      TensorProduct.AlgebraTensorModule.lTensor_tmul, piBaseChangeEquiv_tmul]

/-- **The intertwiner kernels correspond under the identification of the ambient spaces.** Pulling
the kernel of the base-changed defect back along `TauCeti.homBaseChangeEquiv` gives the kernel of
the scalar extension of the defect. -/
private theorem comap_ker_intertwiningDefect_baseChange [Finite G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W) :
    Submodule.comap (homBaseChangeEquiv K L V W : L ⊗[K] (V →ₗ[K] W) →ₗ[L] _)
        (LinearMap.ker (intertwiningDefect (_root_.Representation.baseChange L ρ)
          (_root_.Representation.baseChange L σ)))
      = LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor L L
          (intertwiningDefect ρ σ)) := by
  classical
  let _ := Fintype.ofFinite G
  ext x
  simp [LinearMap.mem_ker, intertwiningDefect_homBaseChangeEquiv,
    (piBaseChangeEquiv K L V W G).map_eq_zero_iff]

/-- **The kernel of a base-changed linear map has the dimension of the original kernel.** `L` is
flat over `K`, so the kernel of the extended map is the extension of the kernel
(`LinearMap.tensorKerEquiv`), whose dimension over `L` is that of the kernel over `K`. -/
private theorem finrank_ker_lTensor {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
    [Module K N] (f : M →ₗ[K] N) :
    Module.finrank L (LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor L L f))
      = Module.finrank K (LinearMap.ker f) :=
  ((LinearMap.tensorKerEquiv L L f).finrank_eq).symm.trans Module.finrank_baseChange

/-- **The kernel of the intertwining defect commutes with scalar extension.** The identification
`TauCeti.homBaseChangeEquiv` of the two ambient spaces carries one kernel onto the other
(`TauCeti.comap_ker_intertwiningDefect_baseChange`), and taking a kernel commutes with the
extension because `L` is flat over `K` (`TauCeti.finrank_ker_lTensor`), so the two dimensions
agree. -/
private theorem finrank_ker_intertwiningDefect_baseChange [Finite G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W) :
    Module.finrank L (LinearMap.ker (intertwiningDefect
        (_root_.Representation.baseChange L ρ) (_root_.Representation.baseChange L σ)))
      = Module.finrank K (LinearMap.ker (intertwiningDefect ρ σ)) :=
  calc Module.finrank L (LinearMap.ker (intertwiningDefect
        (_root_.Representation.baseChange L ρ) (_root_.Representation.baseChange L σ)))
      -- transport the kernel along the identification of the ambient spaces
      = Module.finrank L (Submodule.comap
          (homBaseChangeEquiv K L V W : L ⊗[K] (V →ₗ[K] W) →ₗ[L] _)
          (LinearMap.ker (intertwiningDefect (_root_.Representation.baseChange L ρ)
            (_root_.Representation.baseChange L σ)))) :=
        ((LinearEquiv.ofSubmodule' (homBaseChangeEquiv K L V W) _).finrank_eq).symm
    _ = Module.finrank L (LinearMap.ker (TensorProduct.AlgebraTensorModule.lTensor L L
          (intertwiningDefect ρ σ))) := by
        rw [comap_ker_intertwiningDefect_baseChange]
    _ = Module.finrank K (LinearMap.ker (intertwiningDefect ρ σ)) := finrank_ker_lTensor _

/-- **Base change preserves the dimension of an intertwiner space.** An intertwiner is a linear
map annihilated by the finite family of linear conditions `σ g ∘ₗ f = f ∘ₗ ρ g`, so the intertwiner
space is the kernel of a single linear map; `L` is flat over `K`, so extending the scalars commutes
with taking that kernel (`LinearMap.tensorKerEquiv`), leaving the dimension unchanged. Only the
dimensions are compared here; the underlying identification of the two intertwiner spaces is not
exposed. The dimension alone is what makes an absolutely irreducible representation stay
irreducible after extending the scalars: a one-dimensional endomorphism algebra stays
one-dimensional. -/
theorem _root_.Representation.finrank_intertwiningMap_baseChange [Finite G]
    (ρ : _root_.Representation K G V) (σ : _root_.Representation K G W) :
    Module.finrank L (_root_.Representation.IntertwiningMap
        (_root_.Representation.baseChange L ρ) (_root_.Representation.baseChange L σ))
      = Module.finrank K (_root_.Representation.IntertwiningMap ρ σ) := by
  -- both intertwiner spaces are kernels of the intertwining defect, and those kernels have the
  -- same dimension because `L` is flat over `K`
  rw [(intertwiningMapEquivKerDefect (_root_.Representation.baseChange L ρ)
      (_root_.Representation.baseChange L σ)).finrank_eq,
    (intertwiningMapEquivKerDefect ρ σ).finrank_eq]
  exact finrank_ker_intertwiningDefect_baseChange ρ σ

end Intertwiner

section PermutationRepresentation

open TensorProduct

section Transport

variable {R : Type*} [CommSemiring R] {G : Type*} [Monoid G]
  {V W : Type*} [AddCommMonoid V] [Module R V] [AddCommMonoid W] [Module R W]
  {ρ : _root_.Representation R G V} {σ : _root_.Representation R G W}

/-- **Base change transports an equivalence of representations**: an equivariant isomorphism
`ρ ≃ σ` becomes an equivariant isomorphism `A ⊗[R] V ≃ A ⊗[R] W` after extending the scalars,
because the extension acts on the second factor, where the equivalence already intertwines the
two actions. -/
def _root_.Representation.Equiv.baseChange (φ : ρ.Equiv σ) (A : Type*) [CommSemiring A]
    [Algebra R A] :
    (_root_.Representation.baseChange A ρ).Equiv (_root_.Representation.baseChange A σ) :=
  _root_.Representation.Equiv.mk
    (AlgebraTensorModule.congr (LinearEquiv.refl A A) φ.toLinearEquiv) fun g => by
      ext a
      simp [φ.toIntertwiningMap.isIntertwining]

/-- A base-changed equivalence acts on the second factor of a pure tensor. -/
@[simp]
theorem _root_.Representation.Equiv.baseChange_tmul (φ : ρ.Equiv σ) (A : Type*) [CommSemiring A]
    [Algebra R A] (a : A) (v : V) : φ.baseChange A (a ⊗ₜ[R] v) = a ⊗ₜ[R] φ v :=
  (rfl)

end Transport

section PermutationModule

variable (R : Type*) [CommSemiring R] (A : Type*) [CommSemiring A] [Algebra R A]
  (G : Type*) [Monoid G] (X : Type*) [MulAction G X]

/-- The scalar extension `A ⊗[R] R[X] ≃ₗ[A] A[X]` of the free module on the basis `X`, read
through the coefficients. It is the linear map underlying `TauCeti.baseChangeOfMulActionEquiv`,
which is the interface; this is the implementation step behind it. -/
private noncomputable def monoidAlgebraBaseChangeEquiv :
    A ⊗[R] MonoidAlgebra R X ≃ₗ[A] MonoidAlgebra A X :=
  letI := Classical.decEq X
  AlgebraTensorModule.congr (LinearEquiv.refl A A) (MonoidAlgebra.coeffLinearEquiv R) ≪≫ₗ
    TensorProduct.finsuppScalarRight R A A X ≪≫ₗ (MonoidAlgebra.coeffLinearEquiv A).symm

variable {R A X}

private theorem monoidAlgebraBaseChangeEquiv_tmul_single (a : A) (x : X) (r : R) :
    monoidAlgebraBaseChangeEquiv R A X (a ⊗ₜ[R] MonoidAlgebra.single x r)
      = MonoidAlgebra.single x (r • a) := by
  classical
  rw [← MonoidAlgebra.coeff_inj]
  ext i
  simp [monoidAlgebraBaseChangeEquiv, Finsupp.single_apply, ite_smul]

variable (R A X)

/-- **The base change of a permutation representation is the permutation representation over the
larger ring**: extending the scalars of `R[X]` along `R → A` gives `A[X]`, equivariantly for a
monoid acting on `X`. Both sides are free on the basis `X` and the identification matches those
basis vectors, which the two actions permute in the same way. -/
noncomputable def baseChangeOfMulActionEquiv :
    (_root_.Representation.baseChange A (_root_.Representation.ofMulAction R G X)).Equiv
      (_root_.Representation.ofMulAction A G X) :=
  _root_.Representation.Equiv.mk (monoidAlgebraBaseChangeEquiv R A X) fun g => by
    ext a x
    simp [monoidAlgebraBaseChangeEquiv_tmul_single]

variable {R A X}

/-- `TauCeti.baseChangeOfMulActionEquiv` on the pure tensors spanning the scalar extension. -/
@[simp]
theorem baseChangeOfMulActionEquiv_tmul_single (a : A) (x : X) (r : R) :
    baseChangeOfMulActionEquiv R A G X (a ⊗ₜ[R] MonoidAlgebra.single x r)
      = MonoidAlgebra.single x (r • a) :=
  monoidAlgebraBaseChangeEquiv_tmul_single a x r

/-- `TauCeti.baseChangeOfMulActionEquiv` carries the basis of `A[X]` back to the basis of
`A ⊗[R] R[X]`. -/
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

variable {R : Type*} [CommSemiring R] {A : Type*} [CommSemiring A] [Algebra R A]
  {G : Type*} [Monoid G] {X : Type*} [MulAction G X]

/-- **Pushing the support forward commutes with the coefficientwise scalars.** This is what makes
the permutation module `X →₀ R`, with the action of `Finsupp.comapDistribMulAction`, a
representation of `G` over `R`; it is stated as an instance so that
`Representation.ofDistribMulAction` can be formed wherever that action is a local instance. -/
theorem comapSMulCommClass : SMulCommClass G R (X →₀ R) where
  smul_comm g r f := by
    simp only [Finsupp.comapSMul_def]
    exact Finsupp.mapDomain_smul (f := (g • ·)) r f

attribute [local instance] comapSMulCommClass

variable (R G X)

/-- **The permutation module on a `G`-set is the permutation representation.** The `G`-module
`X →₀ R`, whose action pushes the support forward (`Finsupp.comapDistribMulAction`), is
`Representation.ofMulAction R G X` read through the coefficients: this is the bridge between the
unbundled `DistribMulAction` form of a permutation module and the bundled representation. -/
noncomputable def ofDistribMulActionComapEquiv :
    (_root_.Representation.ofDistribMulAction R G (X →₀ R)).Equiv
      (_root_.Representation.ofMulAction R G X) :=
  _root_.Representation.Equiv.mk (MonoidAlgebra.coeffLinearEquiv R).symm fun g => by
    ext x r
    simp [Finsupp.comapSMul_def]

variable {R X}

/-- `TauCeti.ofDistribMulActionComapEquiv` is the identification of coefficients. -/
@[simp]
theorem ofDistribMulActionComapEquiv_single (x : X) (r : R) :
    ofDistribMulActionComapEquiv R G X (Finsupp.single x r) = MonoidAlgebra.single x r :=
  (rfl)

variable (R A X)

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
  have h : baseChangeComapEquiv R A G X (a ⊗ₜ[R] Finsupp.single x r)
      = baseChangeOfMulActionEquiv R A G X (a ⊗ₜ[R] MonoidAlgebra.single x r) := (rfl)
  rw [h, baseChangeOfMulActionEquiv_tmul_single]

end Comap

end PermutationRepresentation

end TauCeti

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Expect
public import TauCeti.LinearAlgebra.End.Invariant
public import TauCeti.LinearAlgebra.Prod
public import TauCeti.RepresentationTheory.CharacterTable.GLn.HallAlgebra.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Quotient.Card
import TauCeti.GroupTheory.Coset.Fiber
import TauCeti.LinearAlgebra.Quotient.Lift

/-!
# Block averages in the Hall algebra and Mackey's formula

For a class function `A` on all square matrices over a finite field `k` and two classes `a` on
`V_a`, `b` on `V_b`, the *block average* `δA(a, b)` is the mean, over the maps
`x : V_b → V_a`, of `A` at the class of the block upper triangular endomorphism
`(v, w) ↦ (a v + x w, b w)` of `V_a × V_b`. *Mackey's formula* says that `δ` turns the induction
product into the induction product in the second variable:
`δ(A ∗ A′)(a, b) = Σ_W (δA(a|_W, ·) ∗ δA′(a|_{V/W}, ·))(b)`, the sum over the `a`-invariant
subspaces `W` of `V_a`.

## Main definitions

* `TauCeti.HallAlgebra.blockAverage A a`: the function `δA(a, ·)`.
* `TauCeti.HallAlgebra.IsCuspidal A`: `δA(a, b) = 0` whenever `a` and `b` both have positive size.

## Main results

* `TauCeti.HallAlgebra.blockAverage_ofEnd`: the block average at the classes of any `a`, `b` is
  the mean over all maps `x : W →ₗ[k] V`, whatever the representatives.
* `TauCeti.HallAlgebra.blockAverage_mul`: Mackey's formula. The invariant subspaces `U` of the
  block map of `x` are parametrised by a pair `(A, B)` of invariant subspaces of `a` and `b`, the
  class of a shear `(v, w) ↦ (v + s w, w)` modulo the maps taking `B` into `A`, and a map `y`
  taking `B` into `A`, with `x = a s - s b + y`; then `U` is the preimage of `A × B` under the
  shear, and the mean over `y` and `s` of the term of `U` is the mean over the maps `B → A` and
  `V_b ⧸ B → V_a ⧸ A` that `y` induces.
* `TauCeti.HallAlgebra.blockAverage_of_dim_eq_zero_left`,
  `TauCeti.HallAlgebra.blockAverage_of_dim_eq_zero_right`: with a block of size `0` the block
  average is the value at the other block; `TauCeti.HallAlgebra.blockAverage_eq_self_of_dim_eq_zero`
  is the first as an equation of functions.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447.
* A. V. Zelevinsky, *Representations of finite classical groups: a Hopf algebra approach*,
  Lecture Notes in Math. 869 (1981).
* Adapted from `src/Lib/LocalGL/Green/HallAlgebra.lean` in grh-lean
  (https://github.com/lsernau/grh-lean, Apache 2.0, Copyright 2026 Anthropic PBC):
  `New.Hall.blockAverage`, `New.Hall.IsCuspidal`, `New.Hall.blockAverage_simClassOf`,
  `New.Hall.blockAverage_mul` and `New.Hall.blockAverage_of_dim_eq_zero`, here with the
  invariant block first. The block maps `Module.End.blockTriangular` (`New.blockTriangularEnd`)
  and the shears `LinearMap.shear` are in `TauCeti.LinearAlgebra.Prod`, and the lifting
  lemma `Submodule.exists_restrict_eq_and_mapQ_eq` (`New.Hall.exists_restrict_eq_and_mapQ_eq`) is
  in `TauCeti.LinearAlgebra.Quotient.Lift`.
-/

public section

open Module TauCeti.SimilarityClass
open scoped BigOperators

open Module.End (blockTriangular blockTriangular_apply)
open LinearMap (shear)

namespace TauCeti

namespace HallAlgebra

variable {k : Type*} [Field k] [Fintype k]

/-- The *block average* `δA(a, ·)`: at a class `b`, the mean over the matrices `X` of `A` at the
class of the block upper triangular endomorphism with diagonal blocks the chosen representatives
of `a` and `b` and upper right block `X`. By `blockAverage_ofEnd` any representatives give the
same mean. -/
noncomputable def blockAverage (F : HallAlgebra k) (a : SimilarityClass k) : HallAlgebra k :=
  fun b ↦ 𝔼 X : Matrix (Fin a.dim) (Fin b.dim) k,
    F (ofEnd (blockTriangular a.rep b.rep (Matrix.toLin' X)))

/-- A class function is *cuspidal* if its block averages vanish whenever both blocks have
positive size. -/
def IsCuspidal (F : HallAlgebra k) : Prop :=
  ∀ a b : SimilarityClass k, a.dim ≠ 0 → b.dim ≠ 0 → blockAverage F a b = 0

/-- A class function is cuspidal if and only if its block averages vanish whenever both
blocks have positive size. -/
theorem isCuspidal_iff {F : HallAlgebra k} :
    F.IsCuspidal ↔ ∀ a b : SimilarityClass k, a.dim ≠ 0 → b.dim ≠ 0 → blockAverage F a b = 0 :=
  Iff.rfl

/-- The block averages of a cuspidal function vanish when both blocks have positive size. -/
theorem IsCuspidal.blockAverage_eq_zero {F : HallAlgebra k} (hF : F.IsCuspidal)
    {a b : SimilarityClass k} (ha : a.dim ≠ 0) (hb : b.dim ≠ 0) : blockAverage F a b = 0 :=
  hF a b ha hb

/-- The block average of `0` is `0`. -/
@[simp]
theorem blockAverage_zero (a : SimilarityClass k) : blockAverage (0 : HallAlgebra k) a = 0 :=
  ext fun _ ↦ by simp [blockAverage]

/-- The block average is additive in the function. -/
@[simp]
theorem blockAverage_add (F H : HallAlgebra k) (a : SimilarityClass k) :
    blockAverage (F + H) a = blockAverage F a + blockAverage H a :=
  ext fun _ ↦ by simp [blockAverage, Finset.expect_add_distrib]

/-- The block average commutes with complex scalars. -/
@[simp]
theorem blockAverage_smul (c : ℂ) (F : HallAlgebra k) (a : SimilarityClass k) :
    blockAverage (c • F) a = c • blockAverage F a :=
  ext fun _ ↦ by simp [blockAverage, Finset.mul_expect]

variable {V W : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup W] [Module k W] [Module.Finite k W]

/-- The block average at the classes of `a` and `b` is the mean of `A` over the block maps
`blockTriangular a b x` for all `x : W →ₗ[k] V`. -/
theorem blockAverage_ofEnd (F : HallAlgebra k) (a : Module.End k V) (b : Module.End k W)
    [Fintype (W →ₗ[k] V)] :
    blockAverage F (ofEnd a) (ofEnd b) =
      𝔼 x : W →ₗ[k] V, F (ofEnd (blockTriangular a b x)) := by
  -- Isomorphisms `e`, `f` carry the chosen representatives to `a` and `b`, and `e × f`
  -- conjugates the block maps.
  obtain ⟨e, he⟩ := ofEnd_eq_iff.1 (ofEnd_rep (ofEnd a))
  obtain ⟨f, hf⟩ := ofEnd_eq_iff.1 (ofEnd_rep (ofEnd b))
  let E : Matrix (Fin (ofEnd a).dim) (Fin (ofEnd b).dim) k ≃ (W →ₗ[k] V) :=
    Matrix.toLin'.toEquiv.trans (f.arrowCongr e).toEquiv
  refine Fintype.expect_equiv E _ _ fun X ↦
    congrArg F (ofEnd_eq_of_apply_eq (e.prodCongr f) fun p ↦ ?_)
  simp [E, he, hf, LinearEquiv.arrowCongr_apply]

/-- With a first block of size `0`, the block average is the value at the second block. -/
theorem blockAverage_of_dim_eq_zero_left (F : HallAlgebra k) {o : SimilarityClass k}
    (h : o.dim = 0) (a : SimilarityClass k) : blockAverage F o a = F a := by
  have : IsEmpty (Fin o.dim) := by rw [h]; infer_instance
  -- Each block map is similar to the representative of `a`.
  have h_class (X : Matrix (Fin o.dim) (Fin a.dim) k) :
      ofEnd (blockTriangular o.rep a.rep (Matrix.toLin' X)) = a := by
    conv_rhs => rw [← ofEnd_rep a]
    exact ofEnd_eq_of_apply_eq LinearEquiv.uniqueProd fun p ↦ by
      simp [Subsingleton.elim (o.rep p.1 + _) 0]
  simp [blockAverage, h_class]

/-- With a first block of size `0`, the block average is the function itself. -/
theorem blockAverage_eq_self_of_dim_eq_zero (F : HallAlgebra k) {o : SimilarityClass k}
    (h : o.dim = 0) : blockAverage F o = F :=
  ext fun a ↦ blockAverage_of_dim_eq_zero_left F h a

/-- With a second block of size `0`, the block average is the value at the first block. -/
theorem blockAverage_of_dim_eq_zero_right (F : HallAlgebra k) {o : SimilarityClass k}
    (h : o.dim = 0) (a : SimilarityClass k) : blockAverage F a o = F a := by
  have : IsEmpty (Fin o.dim) := by rw [h]; infer_instance
  have h_class (X : Matrix (Fin a.dim) (Fin o.dim) k) :
      ofEnd (blockTriangular a.rep o.rep (Matrix.toLin' X)) = a := by
    conv_rhs => rw [← ofEnd_rep a]
    exact ofEnd_eq_of_apply_eq (LinearEquiv.prodUnique) fun p ↦ by
      simp [Subsingleton.elim p.2 0]
  simp [blockAverage, h_class]

/-! ### Mackey's formula -/

section Mackey

variable (a : Module.End k V) (b : Module.End k W)

omit [Fintype k] in
/-- Linear maps between finite-dimensional spaces over a finite field form a finite set. -/
private local instance finite_linearMap [Finite k] {M N : Type*} [AddCommGroup M] [Module k M]
    [Module.Finite k M] [AddCommGroup N] [Module k N] [Module.Finite k N] : Finite (M →ₗ[k] N) :=
  Module.finite_of_finite k

omit [Fintype k] in
/-- A quotient of a finite module is finite. -/
private local instance finite_quotient {M : Type*} [AddCommGroup M] [Module k M] [Finite M]
    (p : Submodule k M) : Finite (M ⧸ p) :=
  Finite.of_surjective _ p.mkQ_surjective

attribute [local instance low] Fintype.ofFinite

/-- The maps `W → V` that take `B` into `A`, for a pair `P = (A, B)` of invariant subspaces. -/
private abbrev compat (P : a.invtSubmodule × b.invtSubmodule) : Submodule k (W →ₗ[k] V) :=
  P.2.val.compatibleMaps P.1.val

/-- The parametrisation of the pairs `(x, U)`, `U` invariant under the block map of `x`: a pair
`P = (A, B)`, a map `y` taking `B` into `A` and a class `s` of shears give
`x = a s - s b + y` and the preimage of `A × B` under the shear by `s`. -/
private noncomputable def mackeyParam :
    (Σ P : a.invtSubmodule × b.invtSubmodule, compat a b P × ((W →ₗ[k] V) ⧸ compat a b P)) →
      Σ x : W →ₗ[k] V, (blockTriangular a b x).invtSubmodule
  | ⟨P, y, s⟩ => ⟨a ∘ₗ s.out - s.out ∘ₗ b + y.val,
      ⟨_, Submodule.comap_mem_invtSubmodule (shear s.out).toLinearMap
        (LinearMap.shear_blockTriangular a b _ _)
        (Module.End.prod_mem_invtSubmodule_blockTriangular P.1.prop P.2.prop
          ((Submodule.mem_compatibleMaps _ _).1 y.prop))⟩⟩

omit [Fintype k] [Module.Finite k V] [Module.Finite k W] in
private theorem mem_mackeyParam (P : a.invtSubmodule × b.invtSubmodule) (y : compat a b P)
    (s : (W →ₗ[k] V) ⧸ compat a b P) (v : V) (w : W) :
    (v, w) ∈ (mackeyParam a b ⟨P, y, s⟩).2.val ↔ v + s.out w ∈ P.1.val ∧ w ∈ P.2.val := by
  simp [mackeyParam, Submodule.mem_prod]

omit [Fintype k] [Module.Finite k V] [Module.Finite k W] in
private theorem mackeyParam_injective : Function.Injective (mackeyParam a b) := by
  rintro ⟨⟨A, B⟩, y, s⟩ ⟨⟨A', B'⟩, y', s'⟩ h
  obtain ⟨hx, hU⟩ := Sigma.subtype_ext_iff.1 h
  have mem_iff (v : V) (w : W) :
      v + s.out w ∈ A.val ∧ w ∈ B.val ↔ v + s'.out w ∈ A'.val ∧ w ∈ B'.val := by
    rw [← mem_mackeyParam a b (A, B) y, ← mem_mackeyParam a b (A', B') y', hU]
  obtain rfl : A = A' := Subtype.ext (SetLike.ext fun v ↦ by simpa using mem_iff v 0)
  -- At `v = -s w` the left side holds for `w ∈ B`, and at `v = -s' w` the right side for `w ∈ B'`.
  have h_left (w : W) (hw : w ∈ B.val) : -s.out w + s'.out w ∈ A.val ∧ w ∈ B'.val :=
    (mem_iff (-s.out w) w).1 ⟨by simp, hw⟩
  have h_right (w : W) (hw : w ∈ B'.val) : w ∈ B.val :=
    ((mem_iff (-s'.out w) w).2 ⟨by simp, hw⟩).2
  obtain rfl : B = B' :=
    Subtype.ext (SetLike.ext fun w ↦ ⟨fun hw ↦ (h_left w hw).2, h_right w⟩)
  -- The two shears differ by a map taking `B` into `A`, so their classes agree.
  obtain rfl : s = s' := by
    rw [← Submodule.Quotient.mk_out s, ← Submodule.Quotient.mk_out s', Submodule.Quotient.eq]
    intro w hw
    simpa [neg_add_eq_sub] using neg_mem (h_left w hw).1
  obtain rfl : y = y' := Subtype.ext (by simpa [mackeyParam] using hx)
  rfl


omit [Fintype k] [Module.Finite k V] [Module.Finite k W] in
private theorem mackeyParam_surjective : Function.Surjective (mackeyParam a b) := by
  rintro ⟨x, U⟩
  -- `A` is the preimage of `U` under `inl` and `B` the image of `U` under `snd`.
  let A : a.invtSubmodule :=
    ⟨_, Submodule.comap_mem_invtSubmodule (LinearMap.inl k V W) (by simp) U.prop⟩
  have hB : U.val.map (LinearMap.snd k V W) ∈ b.invtSubmodule := by
    refine (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).2 ?_
    rintro _ ⟨z, hz, rfl⟩
    exact ⟨_, (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 U.prop z hz, by simp⟩
  let B : b.invtSubmodule := ⟨_, hB⟩
  -- A map `t : W → U` extending a section of `snd : U → B`; `s` is the class of `-fst ∘ t`.
  obtain ⟨r, hr⟩ := Module.projective_lifting_property _ LinearMap.id
    ((LinearMap.snd k V W).submoduleMap_surjective U.val)
  obtain ⟨t, rfl⟩ := r.exists_extend
  have t_snd (w : W) (hw : w ∈ B.val) : (t w).val.2 = w := congr($hr ⟨w, hw⟩)
  let s := (compat a b (A, B)).mkQ (-(LinearMap.fst k V W ∘ₗ U.val.subtype ∘ₗ t))
  -- For `w ∈ B` the vector `(-s w, w)` lies in `U`.
  have graph_mem (w : W) (hw : w ∈ B.val) : (-s.out w, w) ∈ U.val := by
    have h_out : s.out - _ ∈ compat a b (A, B) :=
      (Submodule.Quotient.eq _).1 (Submodule.Quotient.mk_out s)
    have h_mem : (s.out w + (t w).val.1, (0 : W)) ∈ U.val := by
      simpa [A, sub_eq_add_neg] using h_out hw
    have h_eq : (-s.out w, w) = (t w).val - (s.out w + (t w).val.1, 0) := by
      ext <;> simp [t_snd w hw]
    rw [h_eq]
    exact sub_mem (t w).prop h_mem
  have mem_U (v : V) (w : W) : v + s.out w ∈ A.val ∧ w ∈ B.val ↔ (v, w) ∈ U.val := by
    refine ⟨fun ⟨hv, hw⟩ ↦ ?_, fun h ↦ ⟨?_, ⟨_, h, rfl⟩⟩⟩
    · have h_eq : (v, w) = (v + s.out w, 0) + (-s.out w, w) := by ext <;> simp
      rw [h_eq]
      exact add_mem (Submodule.mem_comap.1 hv) (graph_mem w hw)
    · have h_eq : (v, w) - (-s.out w, w) = (v + s.out w, 0) := by ext <;> simp
      have := sub_mem h (graph_mem w ⟨_, h, rfl⟩)
      rw [h_eq] at this
      exact Submodule.mem_comap.2 this
  -- `y = x - (a s - s b)` takes `B` into `A`.
  have hy : x - (a ∘ₗ s.out - s.out ∘ₗ b) ∈ compat a b (A, B) := fun w hw ↦ by
    have h_mem := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem _).1 U.prop _
      (graph_mem w hw)
    rw [blockTriangular_apply] at h_mem
    have h_eq : a (-s.out w) + x w + s.out (b w) = (x - (a ∘ₗ s.out - s.out ∘ₗ b)) w := by
      simp only [map_neg, LinearMap.sub_apply, LinearMap.comp_apply]
      abel
    exact Submodule.mem_comap.2 (h_eq ▸ ((mem_U _ _).2 h_mem).1)
  refine ⟨⟨(A, B), ⟨_, hy⟩, s⟩, Sigma.subtype_ext (add_sub_cancel _ _) ?_⟩
  exact SetLike.ext fun ⟨v, w⟩ ↦ (mem_mackeyParam a b (A, B) _ s v w).trans (mem_U v w)

/-- The maps `B → A` and `W ⧸ B → V ⧸ A` induced by a map `y` taking `B` into `A`. -/
private def induced (P : a.invtSubmodule × b.invtSubmodule) :
    compat a b P × ((W →ₗ[k] V) ⧸ compat a b P) →+
      (P.2.val →ₗ[k] P.1.val) × (W ⧸ P.2.val →ₗ[k] V ⧸ P.1.val) :=
  AddMonoidHom.mk' (fun z ↦
      (z.1.val.restrict fun _ hw ↦ (Submodule.mem_compatibleMaps _ _).1 z.1.prop hw,
      P.2.val.mapQ P.1.val z.1.val ((Submodule.mem_compatibleMaps _ _).1 z.1.prop))) fun z z' ↦ by
    ext <;> simp [Submodule.mapQ_apply]

omit [Fintype k] [Module.Finite k V] [Module.Finite k W] in
private theorem induced_surjective (P : a.invtSubmodule × b.invtSubmodule) :
    Function.Surjective (induced a b P) := fun ⟨α, β⟩ ↦ by
  obtain ⟨y, hy, hα, hβ⟩ := Submodule.exists_restrict_eq_and_mapQ_eq α β
  exact ⟨(⟨y, hy⟩, 0), Prod.ext hα hβ⟩

/-- The term of the pair `(x, U)` in the expansion of the left side of Mackey's formula. -/
private noncomputable def mackeyTerm (F H : HallAlgebra k)
    (j : Σ x : W →ₗ[k] V, (blockTriangular a b x).invtSubmodule) : ℂ :=
  F (ofEnd ((blockTriangular a b j.1).invtRestrict j.2.prop)) *
    H (ofEnd ((blockTriangular a b j.1).invtQuot j.2.prop))

omit [Fintype k] in
/-- On the pair `(x, U)` given by `P = (A, B)`, `y` and `s`, the block map of `x` on `U` and on
the quotient by `U` has the class of the block map on `A × B`, and on `(V ⧸ A) × (W ⧸ B)`, of
the maps induced by `y`. -/
private theorem mackeyTerm_mackeyParam (F H : HallAlgebra k) (P : a.invtSubmodule × b.invtSubmodule)
    (z : compat a b P × ((W →ₗ[k] V) ⧸ compat a b P)) :
    mackeyTerm a b F H (mackeyParam a b ⟨P, z⟩) =
      F (ofEnd (blockTriangular (a.invtRestrict P.1.prop) (b.invtRestrict P.2.prop)
        (induced a b P z).1)) *
      H (ofEnd (blockTriangular (a.invtQuot P.1.prop) (b.invtQuot P.2.prop)
        (induced a b P z).2)) := by
  obtain ⟨y, s⟩ := z
  have h_sh := LinearMap.shear_blockTriangular a b s.out y.val
  have h_prod := Module.End.prod_mem_invtSubmodule_blockTriangular P.1.prop P.2.prop
    ((Submodule.mem_compatibleMaps _ _).1 y.prop)
  -- The shear identifies the block map of `x` on `U` with the block map of `y` on `A × B`.
  have h_sub : ofEnd ((blockTriangular a b (mackeyParam a b ⟨P, y, s⟩).1).invtRestrict
      (mackeyParam a b ⟨P, y, s⟩).2.prop) =
      ofEnd ((blockTriangular a b y.val).invtRestrict h_prod) :=
    ofEnd_invtRestrict_comap (shear s.out).toLinearMap h_sh (shear s.out).injective h_prod
      (by simp [LinearEquiv.range])
  have h_quot : ofEnd ((blockTriangular a b (mackeyParam a b ⟨P, y, s⟩).1).invtQuot
      (mackeyParam a b ⟨P, y, s⟩).2.prop) =
      ofEnd ((blockTriangular a b y.val).invtQuot h_prod) :=
    ofEnd_invtQuot_comap (shear s.out).toLinearMap h_sh (shear s.out).surjective h_prod
  rw [mackeyTerm, h_sub, h_quot, ofEnd_invtRestrict_eq_of_injective
    (g := blockTriangular (a.invtRestrict P.1.prop) (b.invtRestrict P.2.prop)
      (induced a b P (y, s)).1)
    (P.1.val.subtype.prodMap P.2.val.subtype) (fun _ ↦ by ext <;> simp [induced]) h_prod
    (Prod.map_injective.2 ⟨P.1.val.injective_subtype, P.2.val.injective_subtype⟩)
    (by simp [LinearMap.range_prodMap]),
    ofEnd_invtQuot_eq_of_surjective
    (g' := blockTriangular (a.invtQuot P.1.prop) (b.invtQuot P.2.prop) (induced a b P (y, s)).2)
    (P.1.val.mkQ.prodMap P.2.val.mkQ) (fun _ ↦ by ext <;> simp [induced]) h_prod
    (Prod.map_surjective.2 ⟨P.1.val.mkQ_surjective, P.2.val.mkQ_surjective⟩)
    (by simp [LinearMap.ker_prodMap])]

/-- The left side of Mackey's formula as a sum over the pairs `P = (A, B)` of means over the
maps `y` and the shears `s`. -/
private theorem blockAverage_mul_eq_sum (F H : HallAlgebra k) :
    blockAverage (F * H) (ofEnd a) (ofEnd b) =
      ∑ P : a.invtSubmodule × b.invtSubmodule,
        𝔼 z : compat a b P × ((W →ₗ[k] V) ⧸ compat a b P),
          mackeyTerm a b F H (mackeyParam a b ⟨P, z⟩) := by
  have : Finite V := Module.finite_of_finite k
  have : Finite W := Module.finite_of_finite k
  -- Expand the product at each block map, and reindex the pairs `(x, U)` by `mackeyParam`.
  have h_card (P : a.invtSubmodule × b.invtSubmodule) : (Fintype.card (W →ₗ[k] V) : ℂ) =
      Fintype.card (compat a b P × ((W →ₗ[k] V) ⧸ compat a b P)) := by
    simp only [← Nat.card_eq_fintype_card, Nat.card_prod,
      Submodule.card_eq_card_quotient_mul_card (compat a b P)]
  simp_rw [blockAverage_ofEnd, mul_ofEnd_eq_sum, Fintype.expect_eq_sum_div_card, ← h_card,
    ← Finset.sum_div]
  congr 1
  rw [← Fintype.sum_sigma (fun i ↦ mackeyTerm a b F H (mackeyParam a b i)),
    Fintype.sum_bijective _ ⟨mackeyParam_injective a b, mackeyParam_surjective a b⟩ _
      (mackeyTerm a b F H) fun _ ↦ rfl, Fintype.sum_sigma]
  -- The two sides differ only in the binder `P` versus the pair `⟨P.1, P.2⟩` and in the
  -- `Fintype` instance chosen for the product of the two index types.
  rfl

/-- The right side of Mackey's formula as a sum over the pairs `P = (A, B)` of means over the
maps `B → A` and `W ⧸ B → V ⧸ A`. -/
private theorem sum_blockAverage_mul_blockAverage_eq (F H : HallAlgebra k) :
    ∑ A : a.invtSubmodule,
        (blockAverage F (ofEnd (a.invtRestrict A.prop)) *
          blockAverage H (ofEnd (a.invtQuot A.prop))) (ofEnd b) =
      ∑ P : a.invtSubmodule × b.invtSubmodule,
        𝔼 z : (P.2.val →ₗ[k] P.1.val) × (W ⧸ P.2.val →ₗ[k] V ⧸ P.1.val),
          F (ofEnd (blockTriangular (a.invtRestrict P.1.prop) (b.invtRestrict P.2.prop) z.1)) *
          H (ofEnd (blockTriangular (a.invtQuot P.1.prop) (b.invtQuot P.2.prop) z.2)) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun A _ ↦ ?_
  rw [mul_ofEnd_eq_sum]
  refine Finset.sum_congr rfl fun B _ ↦ ?_
  rw [blockAverage_ofEnd, blockAverage_ofEnd, Finset.expect_mul_expect,
    ← Finset.univ_product_univ, Finset.expect_product]

/-- **Mackey's formula** for block averages: `δ(A ∗ A′)(a, b)` is the sum, over the
`a`-invariant subspaces `W`, of the induction product of `δA(a|_W, ·)` and `δA′(a|_{V/W}, ·)` at
`b`. -/
theorem blockAverage_mul (F H : HallAlgebra k) :
    blockAverage (F * H) (ofEnd a) (ofEnd b) =
      ∑ᶠ A : a.invtSubmodule,
        (blockAverage F (ofEnd (a.invtRestrict A.prop)) *
          blockAverage H (ofEnd (a.invtQuot A.prop))) (ofEnd b) := by
  have : Finite V := Module.finite_of_finite k
  have : Finite W := Module.finite_of_finite k
  -- For each pair `(A, B)`, the term of `(y, s)` only depends on the maps that `y` induces, and
  -- every pair of such maps occurs equally often.
  rw [finsum_eq_sum_of_fintype, sum_blockAverage_mul_blockAverage_eq, blockAverage_mul_eq_sum]
  refine Finset.sum_congr rfl fun P _ ↦ ?_
  simp_rw [mackeyTerm_mackeyParam]
  exact (induced a b P).expect_comp_of_surjective (induced_surjective a b P)
    (fun z ↦ F (ofEnd (blockTriangular (a.invtRestrict P.1.prop) (b.invtRestrict P.2.prop)
      z.1)) * H (ofEnd (blockTriangular (a.invtQuot P.1.prop) (b.invtQuot P.2.prop) z.2)))

end Mackey

end HallAlgebra

end TauCeti

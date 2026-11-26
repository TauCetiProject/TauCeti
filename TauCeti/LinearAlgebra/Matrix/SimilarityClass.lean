/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.FiniteDimensional
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-!
# Similarity classes of square matrices of all sizes

A *similarity class* over a field `k` is a size `n` together with a conjugacy class of
`n × n` matrices over `k` under `GL_n(k)`. Every endomorphism `g` of a finite-dimensional
`k`-vector space `V`, invertible or not, has a similarity class `ofEnd g`, its matrix in any
basis; two endomorphisms have the same class exactly when a linear isomorphism intertwines them.
These classes index the class functions on all square matrices of the Hall algebra
(`TauCeti.HallAlgebra`).

## Main definitions

* `TauCeti.SimilarityClass k`: the similarity classes of square matrices over `k` of all sizes,
  as `Σ n, ConjClasses (Matrix (Fin n) (Fin n) k)`.
* `TauCeti.SimilarityClass.ofEnd g`: the class of an endomorphism `g`.
* `TauCeti.SimilarityClass.rep c`: a chosen endomorphism of `Fin c.dim → k` in the class `c`.
* `TauCeti.SimilarityClass.charpoly c`: the characteristic polynomial of a class.
* `Module.End.invtRestrict g hW`, `Module.End.invtQuot g hW`: the endomorphisms that `g` induces on
  a `g`-invariant subspace `W` and on `V ⧸ W`.

## Main results

* `TauCeti.SimilarityClass.ofEnd_eq_iff`: two endomorphisms have the same class if and only if a
  linear isomorphism intertwines them.
* `TauCeti.SimilarityClass.ofEnd_invtRestrict_eq_of_injective`,
  `TauCeti.SimilarityClass.ofEnd_invtQuot_eq_of_surjective`: classes on invariant subspaces and
  quotients, computed through an injective or surjective intertwining map.
* `TauCeti.SimilarityClass.ofEnd_dualMap`: every endomorphism of a finite-dimensional vector
  space is similar to its transpose. The proof identifies `V` with a product of cyclic
  `k[X]`-modules `k[X] ⧸ (p)` and each of these with its dual through a nondegenerate form
  `(x, y) ↦ L (x * y)`.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447, §1.
* The similarity classes `New.SimClass`, `New.simClassOf`, `New.SimClass.charpoly`, and the lemmas
  `New.simClassOf_eq_iff`, `New.simClassOf_endOnSub`, `New.simClassOf_endOnQuot`,
  `New.simClassOf_endOnSub_comap`, `New.simClassOf_endOnQuot_comap`,
  `New.exists_nondegenerate_mul_form` and `New.simClassOf_eq_dualMap` of
  `src/Lib/LocalGL/Green/HallAlgebra.lean` in grh-lean (https://github.com/lsernau/grh-lean,
  Apache 2.0, Copyright 2026 Anthropic PBC), here with `Mathlib`'s `ConjClasses` of matrices as
  the carrier.
-/

public section

open Module Polynomial

namespace TauCeti

/-- The similarity classes of square matrices over `k` of all sizes, invertible or not: a size
`n` with a conjugacy class of `n × n` matrices under `GL_n(k)`. -/
abbrev SimilarityClass (k : Type*) [Field k] : Type _ :=
  Σ n : ℕ, ConjClasses (Matrix (Fin n) (Fin n) k)

namespace SimilarityClass

variable {k : Type*} [Field k]

/-- The size of the matrices in a similarity class. -/
abbrev dim (c : SimilarityClass k) : ℕ := c.1

section OfEnd

variable {V V' : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup V'] [Module k V'] [Module.Finite k V']

/-- The similarity class of an endomorphism `g` of a finite-dimensional vector space: the class of
its matrix in a basis. It does not depend on the basis (`ofEnd_eq_mk_toMatrix`). -/
noncomputable def ofEnd (g : Module.End k V) : SimilarityClass k :=
  ⟨finrank k V, .mk (LinearMap.toMatrix (finBasis k V) (finBasis k V) g)⟩

/-- The class of an endomorphism of `V` has size `finrank k V`. -/
@[simp]
theorem dim_ofEnd (g : Module.End k V) : (ofEnd g).dim = finrank k V :=
  (rfl)

/-- The class of `g` is the conjugacy class of the matrix of `g` in any basis. -/
theorem ofEnd_eq_mk_toMatrix {n : ℕ} (b : Basis (Fin n) k V) (g : Module.End k V) :
    ofEnd g = ⟨n, .mk (LinearMap.toMatrix b b g)⟩ := by
  obtain rfl : finrank k V = n := by simpa using finrank_eq_card_basis b
  refine Sigma.ext rfl (heq_of_eq (ConjClasses.mk_eq_mk_iff_isConj.2 ?_))
  -- The change of basis matrices conjugate one matrix of `g` into the other.
  refine ⟨⟨b.toMatrix (finBasis k V), (finBasis k V).toMatrix b, ?_, ?_⟩, ?_⟩
  · exact Basis.toMatrix_mul_toMatrix_flip _ _
  · exact Basis.toMatrix_mul_toMatrix_flip _ _
  · change _ * _ = _ * _
    rw [← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b (finBasis k V) b
      (finBasis k V)]
    simp

/-- The class of the endomorphism `toLin' M` of `Fin n → k` is the conjugacy class of `M`. -/
@[simp]
theorem ofEnd_toLin' {n : ℕ} (M : Matrix (Fin n) (Fin n) k) :
    ofEnd (Matrix.toLin' M) = ⟨n, .mk M⟩ := by
  rw [ofEnd_eq_mk_toMatrix (Pi.basisFun k (Fin n)), LinearMap.toMatrix_eq_toMatrix',
    LinearMap.toMatrix'_toLin']

/-- Endomorphisms intertwined by a linear isomorphism have the same class. -/
theorem ofEnd_eq_of_apply_eq {g : Module.End k V} {g' : Module.End k V'} (e : V ≃ₗ[k] V')
    (he : ∀ x, e (g x) = g' (e x)) : ofEnd g = ofEnd g' := by
  -- In the basis of `V` transported from a basis of `V'`, `g` has the matrix of `g'`.
  let b' := (finBasis k V').reindex (finCongr e.finrank_eq.symm)
  rw [ofEnd_eq_mk_toMatrix (b'.map e.symm), ofEnd_eq_mk_toMatrix b']
  congr 2
  ext i j
  simp [LinearMap.toMatrix_apply, he]

/-- The class of `e.conj g` is the class of `g`. -/
@[simp]
theorem ofEnd_conj (e : V ≃ₗ[k] V') (g : Module.End k V) : ofEnd (e.conj g) = ofEnd g :=
  (ofEnd_eq_of_apply_eq e (by simp)).symm

/-- Two endomorphisms have the same similarity class if and only if a linear isomorphism
intertwines them. -/
theorem ofEnd_eq_iff {g : Module.End k V} {g' : Module.End k V'} :
    ofEnd g = ofEnd g' ↔ ∃ e : V ≃ₗ[k] V', ∀ x, e (g x) = g' (e x) := by
  refine ⟨fun h ↦ ?_, fun ⟨e, he⟩ ↦ ofEnd_eq_of_apply_eq e he⟩
  -- Write both classes with matrices of the same size; a conjugating matrix gives `e`.
  have hdim : finrank k V = finrank k V' := by simpa using congrArg dim h
  let b := finBasis k V
  let b' := (finBasis k V').reindex (finCongr hdim.symm)
  rw [ofEnd_eq_mk_toMatrix b, ofEnd_eq_mk_toMatrix b', Sigma.mk.inj_iff] at h
  obtain ⟨P, hP⟩ := ConjClasses.mk_eq_mk_iff_isConj.1 (eq_of_heq h.2)
  let e : V ≃ₗ[k] V' :=
    { Matrix.toLin b b' P with
      invFun := Matrix.toLin b' b ↑P⁻¹
      left_inv x := by
        simp [← LinearMap.comp_apply, ← Matrix.toLin_mul]
      right_inv x := by
        simp [← LinearMap.comp_apply, ← Matrix.toLin_mul] }
  refine ⟨e, fun x ↦ ?_⟩
  have hcomp : Matrix.toLin b b' P ∘ₗ g = g' ∘ₗ Matrix.toLin b b' P := by
    apply (LinearMap.toMatrix b b').injective
    rw [LinearMap.toMatrix_comp b b b', LinearMap.toMatrix_comp b b' b', LinearMap.toMatrix_toLin]
    exact hP
  exact LinearMap.congr_fun hcomp x

/-- Endomorphisms of a zero-dimensional space all have the same class. -/
theorem ofEnd_eq_of_finrank_eq_zero {g : Module.End k V} {g' : Module.End k V'}
    (h : finrank k V = 0) (h' : finrank k V' = 0) : ofEnd g = ofEnd g' := by
  have := finrank_zero_iff.1 h
  have := finrank_zero_iff.1 h'
  exact ofEnd_eq_of_apply_eq (LinearEquiv.ofSubsingleton V V') (fun _ ↦ Subsingleton.elim _ _)

end OfEnd

/-- A chosen endomorphism of `Fin c.dim → k` in the class `c`. -/
noncomputable def rep (c : SimilarityClass k) : Module.End k (Fin c.dim → k) :=
  Matrix.toLin' (Classical.choose (ConjClasses.exists_rep c.2))

/-- The chosen endomorphism `c.rep` lies in the class `c`. -/
@[simp]
theorem ofEnd_rep (c : SimilarityClass k) : ofEnd c.rep = c := by
  rw [rep, ofEnd_toLin', Classical.choose_spec (ConjClasses.exists_rep c.2)]

/-- Two classes of size `0` are equal. -/
theorem eq_of_dim_eq_zero {c c' : SimilarityClass k} (h : c.dim = 0) (h' : c'.dim = 0) :
    c = c' := by
  rw [← ofEnd_rep c, ← ofEnd_rep c']
  exact ofEnd_eq_of_finrank_eq_zero (by simpa using h) (by simpa using h')

/-- The characteristic polynomial of the matrices in a similarity class. -/
noncomputable def charpoly (c : SimilarityClass k) : k[X] :=
  c.rep.charpoly

/-- The characteristic polynomial of the class of `g` is that of `g`. -/
@[simp]
theorem charpoly_ofEnd {V : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
    (g : Module.End k V) : (ofEnd g).charpoly = g.charpoly := by
  obtain ⟨e, he⟩ := ofEnd_eq_iff.1 (ofEnd_rep (ofEnd g))
  have : e.conj (ofEnd g).rep = g := by
    ext x
    simp [LinearEquiv.conj_apply, he]
  rw [charpoly]
  conv_rhs => rw [← this]
  exact (LinearEquiv.charpoly_conj e _).symm

/-! ### Classes on invariant subspaces and quotients -/

section Invariant

variable {V V' : Type*} [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V']
  {g : Module.End k V} {g' : Module.End k V'}

/-- The restriction of `g` to a `g`-invariant subspace `W`. -/
def _root_.Module.End.invtRestrict (g : Module.End k V) {W : Submodule k V}
    (hW : W ∈ g.invtSubmodule) : Module.End k W :=
  g.restrict ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem g).1 hW)

/-- The endomorphism of `V ⧸ W` induced by `g`, for a `g`-invariant subspace `W`. -/
def _root_.Module.End.invtQuot (g : Module.End k V) {W : Submodule k V}
    (hW : W ∈ g.invtSubmodule) : Module.End k (V ⧸ W) :=
  W.mapQ W g ((Module.End.mem_invtSubmodule g).1 hW)

/-- The restriction of `g` to `W` acts as `g`. -/
@[simp]
theorem _root_.Module.End.coe_invtRestrict_apply {W : Submodule k V} (hW : W ∈ g.invtSubmodule)
    (x : W) : (g.invtRestrict hW x : V) = g x :=
  (rfl)

/-- The map induced on `V ⧸ W` sends the class of `x` to the class of `g x`. -/
@[simp]
theorem _root_.Module.End.invtQuot_mk {W : Submodule k V} (hW : W ∈ g.invtSubmodule) (x : V) :
    g.invtQuot hW (Submodule.Quotient.mk x) = Submodule.Quotient.mk (g x) :=
  (rfl)

variable [Module.Finite k V] [Module.Finite k V']

/-- If `p` is surjective with kernel `W` and intertwines `g` with `g'`, then `g` induces on `V ⧸ W`
an endomorphism of the class of `g'`. -/
theorem ofEnd_invtQuot_eq_of_surjective (p : V →ₗ[k] V') (hp : ∀ x, p (g x) = g' (p x))
    {W : Submodule k V} (hW : W ∈ g.invtSubmodule) (h_surj : Function.Surjective p)
    (h_ker : LinearMap.ker p = W) : ofEnd (g.invtQuot hW) = ofEnd g' := by
  -- `p` induces an isomorphism `V ⧸ W ≃ V'`, which sends the class of `v` to `p v`.
  refine ofEnd_eq_of_apply_eq
    (Submodule.quotEquivOfEq W _ h_ker.symm ≪≫ₗ p.quotKerEquivOfSurjective h_surj) fun x ↦ ?_
  induction x using Submodule.Quotient.induction_on with
  | H v => simpa using hp v

/-- If `p` is injective with image `U` and intertwines `g` with `g'`, then `g'` restricts on `U` to
an endomorphism of the class of `g`. -/
theorem ofEnd_invtRestrict_eq_of_injective (p : V →ₗ[k] V') (hp : ∀ x, p (g x) = g' (p x))
    {U : Submodule k V'} (hU : U ∈ g'.invtSubmodule) (h_inj : Function.Injective p)
    (h_range : LinearMap.range p = U) : ofEnd (g'.invtRestrict hU) = ofEnd g := by
  refine (ofEnd_eq_of_apply_eq (g' := g'.invtRestrict hU)
    (LinearEquiv.ofInjective p h_inj ≪≫ₗ LinearEquiv.ofEq _ _ h_range) fun x ↦ ?_).symm
  exact Subtype.ext (by simpa using hp x)

omit [Module.Finite k V] [Module.Finite k V'] in
/-- The preimage of a `g'`-invariant subspace under a map intertwining `g` with `g'` is
`g`-invariant. -/
theorem _root_.Submodule.comap_mem_invtSubmodule (p : V →ₗ[k] V') (hp : ∀ x, p (g x) = g' (p x))
    {U : Submodule k V'} (hU : U ∈ g'.invtSubmodule) : U.comap p ∈ g.invtSubmodule :=
  (Module.End.mem_invtSubmodule _).2 fun x hx ↦ by
    simpa [hp] using (Module.End.mem_invtSubmodule _).1 hU hx

/-- For an injective map `p` intertwining `g` with `g'`, and a `g'`-invariant subspace `U` in the
image of `p`, the restrictions of `g` to `p⁻¹(U)` and of `g'` to `U` have the same class. -/
theorem ofEnd_invtRestrict_comap (p : V →ₗ[k] V') (hp : ∀ x, p (g x) = g' (p x))
    (h_inj : Function.Injective p) {U : Submodule k V'} (hU : U ∈ g'.invtSubmodule)
    (h_le : U ≤ LinearMap.range p) :
    ofEnd (g.invtRestrict (Submodule.comap_mem_invtSubmodule p hp hU)) =
      ofEnd (g'.invtRestrict hU) :=
  ofEnd_eq_of_apply_eq (Submodule.comap_equiv_self_of_inj_of_le h_inj h_le)
    fun x ↦ Subtype.ext (by simpa using hp x)

/-- For a surjective map `p` intertwining `g` with `g'`, and a `g'`-invariant subspace `U`, the
maps induced by `g` on `V ⧸ p⁻¹(U)` and by `g'` on `V' ⧸ U` have the same class. -/
theorem ofEnd_invtQuot_comap (p : V →ₗ[k] V') (hp : ∀ x, p (g x) = g' (p x))
    (h_surj : Function.Surjective p) {U : Submodule k V'} (hU : U ∈ g'.invtSubmodule) :
    ofEnd (g.invtQuot (Submodule.comap_mem_invtSubmodule p hp hU)) = ofEnd (g'.invtQuot hU) :=
  -- `p` followed by the quotient map is surjective with kernel `p⁻¹(U)`.
  ofEnd_invtQuot_eq_of_surjective (U.mkQ ∘ₗ p) (fun x ↦ by simp [hp]) _
    (U.mkQ_surjective.comp h_surj) (by simp [LinearMap.ker_comp])

end Invariant

end SimilarityClass

/-! ### An endomorphism is similar to its transpose -/

section Transpose

variable {k : Type*} [Field k]

/-- A finite-dimensional quotient `A` of `k[X]` carries a linear form `L` for which the pairing
`(x, y) ↦ L (x * y)` is nondegenerate. -/
private theorem exists_nondegenerate_mul_form (I : Ideal k[X]) [Module.Finite k (k[X] ⧸ I)] :
    ∃ L : Dual k (k[X] ⧸ I),
      LinearMap.BilinForm.Nondegenerate ((LinearMap.mul k (k[X] ⧸ I)).compr₂ L) := by
  -- Let `k[X]` act on the dual by `(q • φ) x = φ (q • x)`. Over a principal ideal domain some `L`
  -- has the same annihilator as the whole module.
  let _ : Module k[X] (Dual k (k[X] ⧸ I)) :=
    Module.compHom _ (R := k[X]ᵈᵐᵃ) (.toOpposite (.id k[X]) .all)
  have _ : IsScalarTower k k[X] (Dual k (k[X] ⧸ I)) := ⟨fun c q φ ↦ by
    ext x
    -- `change` unfolds the action of `k[X]` on the dual, defined just above.
    change φ ((c • q) • x) = c • φ (q • x)
    rw [smul_assoc, map_smul]⟩
  have _ : Module.Finite k[X] (Dual k (k[X] ⧸ I)) := .of_restrictScalars_finite k k[X] _
  obtain ⟨L, hL⟩ : ∃ L : Dual k (k[X] ⧸ I),
      (LinearMap.toSpanSingleton k[X] (Dual k (k[X] ⧸ I)) L).ker =
        Module.annihilator k[X] (Dual k (k[X] ⧸ I)) :=
    Module.exists_ker_toSpanSingleton_eq_annihilator k[X] (Dual k (k[X] ⧸ I))
  refine ⟨L, .ofSeparatingLeft ?_⟩
  rintro ⟨q⟩ hq
  -- If `q` pairs to zero with everything then `q • L = 0`, so `q` kills every linear form `φ`;
  -- evaluating `q • φ = 0` at `1` shows that `φ` vanishes on the class of `q`.
  have h_ann : q ∈ Module.annihilator k[X] (Dual k (k[X] ⧸ I)) := hL.le (LinearMap.ext hq)
  refine (Module.forall_dual_apply_eq_zero_iff k _).mp fun φ ↦ ?_
  have h_eval : φ (q • 1) = 0 := LinearMap.congr_fun (Module.mem_annihilator.mp h_ann φ) 1
  rwa [← mul_one q]

/-- Every endomorphism of a finite-dimensional vector space is similar to its transpose. -/
theorem SimilarityClass.ofEnd_dualMap {V : Type*} [AddCommGroup V] [Module k V]
    [Module.Finite k V] (g : Module.End k V) : ofEnd g.dualMap = ofEnd g := by
  classical
  -- By the structure theorem `V` is a product of cyclic modules `k[X] ⧸ (p i ^ n i)`, with `g`
  -- acting as `X`.
  obtain ⟨ι, _, p, -, n, ⟨e⟩⟩ :=
    Module.equiv_directSum_of_isTorsion (Module.AEval.isTorsion_of_finiteDimensional k V g)
  let E : V ≃ₗ[k] ∀ i, k[X] ⧸ k[X] ∙ p i ^ n i :=
    Module.AEval'.of g ≪≫ₗ (e ≪≫ₗ DFinsupp.linearEquivFunOnFintype).restrictScalars k
  have _ : ∀ i, Module.Finite k (k[X] ⧸ k[X] ∙ p i ^ n i) := Module.Finite.pi_iff.mp (.equiv E)
  -- Each factor is identified with its dual by a pairing `L i (x * y)`; summing over the factors
  -- identifies `V` with its dual.
  choose L hL using fun i ↦ exists_nondegenerate_mul_form (k[X] ∙ p i ^ n i)
  let D : V ≃ₗ[k] Dual k V :=
    E ≪≫ₗ LinearEquiv.piCongrRight (fun i ↦ LinearMap.BilinForm.toDual _ (hL i)) ≪≫ₗ
      LinearMap.lsum k _ k ≪≫ₗ E.dualMap
  -- Multiplication by `X` is self-adjoint for these pairings, so `D` carries `g` to its transpose.
  refine (ofEnd_eq_of_apply_eq D ?_).symm
  simp [D, LinearMap.BilinForm.toDual, LinearMap.ext_iff, E, ← Module.AEval'.X_smul_of,
    smul_mul_assoc, mul_smul_comm]

end Transpose

end TauCeti

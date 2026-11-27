/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Conj
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Semisimple
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import TauCeti.LinearAlgebra.End.Invariant
import Mathlib.Algebra.Module.PID
import Mathlib.Algebra.Polynomial.Module.FiniteDimensional
import TauCeti.LinearAlgebra.BilinearForm.PolynomialQuotient
import TauCeti.LinearAlgebra.Charpoly.Quotient

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

## Main results

* `TauCeti.SimilarityClass.ofEnd_eq_iff`: two endomorphisms have the same class if and only if a
  linear isomorphism intertwines them.
* `TauCeti.SimilarityClass.ofEnd_invtRestrict_eq_of_injective`,
  `TauCeti.SimilarityClass.ofEnd_invtQuot_eq_of_surjective`: classes of the endomorphisms induced
  on invariant subspaces and quotients (`Module.End.invtRestrict`, `Module.End.invtQuot`), computed
  through an injective or surjective intertwining map.
* `TauCeti.SimilarityClass.ofEnd_invtQuot_invtRestrict_comap_mkQ`: for invariant subspaces
  `U ≤ W`, the class of `g` on `W ⧸ U` computed in `V ⧸ U` (third isomorphism theorem).
* `TauCeti.SimilarityClass.ofEnd_dualMap`: every endomorphism of a finite-dimensional vector
  space is similar to its transpose. The proof identifies `V` with a product of cyclic
  `k[X]`-modules `k[X] ⧸ (p)` and each of these with its dual through a nondegenerate form
  `(x, y) ↦ L (x * y)` (`Ideal.exists_nondegenerate_mul_form`).
* `TauCeti.SimilarityClass.ofEnd_invtRestrict_dualAnnihilator`,
  `TauCeti.SimilarityClass.ofEnd_invtQuot_dualAnnihilator`: the transpose of `g` on the annihilator
  of an invariant subspace `W`, and on the quotient by it, has the class of `g` on `V ⧸ W`, and on
  `W`.
* `TauCeti.SimilarityClass.ofEnd_blockTriangular_of_isSemisimple`: a semisimple block triangular
  map is similar to its block diagonal part.
* `Module.End.charpoly_invtRestrict_mul_charpoly_invtQuot`: the characteristic polynomial is the
  product of those on an invariant subspace and on the quotient.

## References

* J. A. Green, *The characters of the finite general linear groups*, Trans. Amer. Math. Soc. 80
  (1955), 402–447, §1.
* The similarity classes `New.SimClass`, `New.simClassOf`, `New.SimClass.charpoly`, and the lemmas
  `New.simClassOf_eq_iff`, `New.simClassOf_endOnSub`, `New.simClassOf_endOnQuot`,
  `New.simClassOf_endOnSub_comap`, `New.simClassOf_endOnQuot_comap` and
  `New.simClassOf_eq_dualMap` of
  `src/Lib/LocalGL/Green/HallAlgebra.lean` in grh-lean (https://github.com/lsernau/grh-lean,
  Apache 2.0, Copyright 2026 Anthropic PBC), here with `Mathlib`'s `ConjClasses` of matrices as
  the carrier.
* Adapted from grh-lean as above: the similarity of a semisimple block triangular map with its
  block diagonal part from `src/Lib/LocalGL/Green/CuspidalFunctions.lean`, here proved with an
  invariant complement of the first summand rather than with a projection.
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
  · rw [SemiconjBy, Units.val_mk,
      ← basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b (finBasis k V) b (finBasis k V)]
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

/-- For `g`-invariant subspaces `U ≤ W`, with `W` the preimage of a subspace `W'` of `V ⧸ U`, the
map that `g` induces on `W ⧸ U` has the class of the restriction to `W'` of the map induced by
`g` on `V ⧸ U`. -/
theorem ofEnd_invtQuot_invtRestrict_comap_mkQ {U : Submodule k V} (hU : U ∈ g.invtSubmodule)
    {W' : Submodule k (V ⧸ U)} (hW' : W' ∈ (g.invtQuot hU).invtSubmodule) :
    ofEnd ((g.invtRestrict (Submodule.comap_mem_invtSubmodule U.mkQ
        (fun x ↦ (g.invtQuot_mk hU x).symm) hW')).invtQuot
        (Submodule.comap_mem_invtSubmodule (W'.comap U.mkQ).subtype
          (g.coe_invtRestrict_apply _) hU)) =
      ofEnd ((g.invtQuot hU).invtRestrict hW') := by
  -- The quotient map `W → W'` is surjective, with kernel `U ∩ W`.
  let p : W'.comap U.mkQ →ₗ[k] W' := (U.mkQ ∘ₗ (W'.comap U.mkQ).subtype).codRestrict W' (·.prop)
  have hp (y : W'.comap U.mkQ) : (p y : V ⧸ U) = U.mkQ y := rfl
  refine ofEnd_invtQuot_eq_of_surjective (g' := (g.invtQuot hU).invtRestrict hW') p ?_ _ ?_ ?_
  · intro x
    apply Subtype.ext
    rw [Module.End.coe_invtRestrict_apply, hp, hp, Module.End.coe_invtRestrict_apply]
    exact (g.invtQuot_mk hU x.val).symm
  · rintro ⟨y, hy⟩
    obtain ⟨v, rfl⟩ := U.mkQ_surjective y
    exact ⟨⟨v, hy⟩, rfl⟩
  · ext x
    exact Subtype.ext_iff.trans ((hp x).symm ▸ Submodule.Quotient.mk_eq_zero U (x := x.val))

end Invariant

/-! ### Block triangular maps -/

section Block

variable {V W : Type*} [AddCommGroup V] [Module k V] [Module.Finite k V]
  [AddCommGroup W] [Module k W] [Module.Finite k W]

open Module.End (blockTriangular blockTriangular_apply) in
/-- A semisimple block upper triangular map `(v, w) ↦ (a v + x w, b w)` is similar to the block
diagonal map `a ⊕ b`. -/
theorem ofEnd_blockTriangular_of_isSemisimple {a : Module.End k V} {b : Module.End k W}
    {x : W →ₗ[k] V} (h : (blockTriangular a b x).IsSemisimple) :
    ofEnd (blockTriangular a b x) = ofEnd (a.prodMap b) := by
  set g := blockTriangular a b x
  -- `V × 0` is invariant; take an invariant complement `C`, which maps isomorphically onto `W`.
  have hK : LinearMap.ker (LinearMap.snd k V W) ∈ g.invtSubmodule :=
    (Module.End.mem_invtSubmodule _).2 fun p hp ↦ by
      simp_all [g, blockTriangular_apply]
  obtain ⟨C, hC, hKC⟩ := Module.End.isSemisimple_iff.1 h _ hK
  -- The second coordinate is an isomorphism from `C` onto `W`.
  have h_inj : Function.Injective (LinearMap.snd k V W ∘ₗ C.subtype) := by
    refine (injective_iff_map_eq_zero _).2 fun c hc ↦ ?_
    have : (c : V × W) ∈ LinearMap.ker (LinearMap.snd k V W) ⊓ C :=
      ⟨LinearMap.mem_ker.2 (by simpa using hc), c.prop⟩
    simpa [hKC.inf_eq_bot] using this
  have h_surj : Function.Surjective (LinearMap.snd k V W ∘ₗ C.subtype) := by
    intro w
    obtain ⟨u, hu, c, hc, huc⟩ := Submodule.mem_sup.1 (hKC.sup_eq_top ▸ Submodule.mem_top :
      ((0, w) : V × W) ∈ LinearMap.ker (LinearMap.snd k V W) ⊔ C)
    refine ⟨⟨c, hc⟩, ?_⟩
    have h₂ : u.2 + c.2 = w := congrArg Prod.snd huc
    have hu₂ : u.2 = 0 := by simpa using LinearMap.mem_ker.1 hu
    simp [← h₂, hu₂]
  let eC := LinearEquiv.ofBijective _ ⟨h_inj, h_surj⟩
  -- `(v, w) ↦ (v, 0) + c(w)`, with `c(w) ∈ C` the element of second coordinate `w`, conjugates
  -- `a ⊕ b` to `g`.
  let φ : Module.End k (V × W) :=
    LinearMap.coprod (LinearMap.inl k V W) (C.subtype ∘ₗ eC.symm.toLinearMap)
  have hφ_snd (w : W) : ((eC.symm w : C) : V × W).2 = w :=
    eC.apply_symm_apply w
  have h_comm (p : V × W) : φ (a.prodMap b p) = g (φ p) := by
    -- `g` preserves `C`, and on `C` it acts on the second coordinate as `b`.
    have hgc : g (eC.symm p.2) = (eC.symm (b p.2) : V × W) := by
      have h_mem : g (eC.symm p.2) ∈ C := (Module.End.mem_invtSubmodule _).1 hC (eC.symm p.2).prop
      have := h_inj (a₁ := ⟨_, h_mem⟩) (a₂ := eC.symm (b p.2)) (by
        simp [hφ_snd, g, blockTriangular_apply])
      exact congrArg Subtype.val this
    simp [φ, map_add, hgc, g, blockTriangular_apply]
  have hφ_inj : Function.Injective φ := by
    refine (injective_iff_map_eq_zero _).2 fun p hp ↦ ?_
    have h₂ : p.2 = 0 := by simpa [φ, hφ_snd] using congrArg Prod.snd hp
    have h₁ : p.1 = 0 := by simpa [φ, h₂] using congrArg Prod.fst hp
    exact Prod.ext h₁ h₂
  exact (ofEnd_eq_of_apply_eq (LinearEquiv.ofInjectiveEndo φ hφ_inj) h_comm).symm

end Block

end SimilarityClass

/-! ### An endomorphism is similar to its transpose -/

section Transpose

variable {k : Type*} [Field k]

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
  choose L hL using fun i ↦ Ideal.exists_nondegenerate_mul_form (k[X] ∙ p i ^ n i)
  let D : V ≃ₗ[k] Dual k V :=
    E ≪≫ₗ LinearEquiv.piCongrRight (fun i ↦ LinearMap.BilinForm.toDual _ (hL i)) ≪≫ₗ
      LinearMap.lsum k _ k ≪≫ₗ E.dualMap
  -- Multiplication by `X` is self-adjoint for these pairings, so `D` carries `g` to its transpose.
  refine (ofEnd_eq_of_apply_eq D ?_).symm
  simp [D, LinearMap.BilinForm.toDual, LinearMap.ext_iff, E, ← Module.AEval'.X_smul_of,
    smul_mul_assoc, mul_smul_comm]

/-- The transpose of `g` on the annihilator of a `g`-invariant subspace `W` has the class of the map
induced by `g` on `V ⧸ W`. -/
theorem SimilarityClass.ofEnd_invtRestrict_dualAnnihilator {V : Type*} [AddCommGroup V]
    [Module k V] [Module.Finite k V] {g : Module.End k V} {W : Submodule k V}
    (hW : W ∈ g.invtSubmodule) :
    ofEnd (V := W.dualAnnihilator)
        (Module.End.invtRestrict g.dualMap (W.dualAnnihilator_mem_invtSubmodule hW)) =
      ofEnd (g.invtQuot hW) := by
  rw [ofEnd_invtRestrict_eq_of_injective (g := (g.invtQuot hW).dualMap) W.mkQ.dualMap
    (fun φ ↦ LinearMap.ext fun v ↦ by simp) _
    (LinearMap.dualMap_injective_of_surjective W.mkQ_surjective) W.range_dualMap_mkQ_eq,
    ofEnd_dualMap]

/-- The map induced by the transpose of `g` on the quotient by the annihilator of a `g`-invariant
subspace `W` has the class of the restriction of `g` to `W`. -/
theorem SimilarityClass.ofEnd_invtQuot_dualAnnihilator {V : Type*} [AddCommGroup V]
    [Module k V] [Module.Finite k V] {g : Module.End k V} {W : Submodule k V}
    (hW : W ∈ g.invtSubmodule) :
    ofEnd (Module.End.invtQuot g.dualMap (W.dualAnnihilator_mem_invtSubmodule hW)) =
      ofEnd (g.invtRestrict hW) := by
  rw [ofEnd_invtQuot_eq_of_surjective (g' := (g.invtRestrict hW).dualMap) W.subtype.dualMap
    (fun φ ↦ LinearMap.ext fun w ↦ by simp) _
    (LinearMap.dualMap_surjective_of_injective W.injective_subtype)
    (by simp [LinearMap.ker_dualMap_eq_dualAnnihilator_range]), ofEnd_dualMap]

end Transpose

end TauCeti

/-- The characteristic polynomial of `g` is the product of those of `g` on an invariant subspace
and on the quotient. -/
theorem Module.End.charpoly_invtRestrict_mul_charpoly_invtQuot {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [Module.Finite k V] {g : Module.End k V} {U : Submodule k V}
    (hU : U ∈ g.invtSubmodule) :
    (g.invtRestrict hU).charpoly * (g.invtQuot hU).charpoly = g.charpoly := by
  open TauCeti.SimilarityClass in
  have hU' := (Module.End.mem_invtSubmodule g).1 hU
  -- Replace the two maps by `LinearMap.restrict` and `Submodule.mapQ`, which have the same
  -- classes; the definitions of `invtRestrict` and `invtQuot` are not exposed here.
  rw [← charpoly_ofEnd (g.invtRestrict hU), ← charpoly_ofEnd (g.invtQuot hU),
    ofEnd_invtRestrict_eq_of_injective (g := g.restrict hU') U.subtype (fun _ ↦ rfl) hU
      U.injective_subtype U.range_subtype,
    ofEnd_invtQuot_eq_of_surjective U.mkQ (g' := U.mapQ U g hU') (fun _ ↦ rfl) hU
      U.mkQ_surjective U.ker_mkQ, charpoly_ofEnd, charpoly_ofEnd,
    LinearMap.charpoly_eq_charpoly_restrict_mul_charpoly_mapQ U g hU']

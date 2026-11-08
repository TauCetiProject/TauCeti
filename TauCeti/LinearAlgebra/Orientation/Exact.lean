/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Basis.Exact
public import TauCeti.LinearAlgebra.Orientation.Prod

/-!
# Orientations of short exact sequences

Let `0 → A → B → C → 0` be a short exact sequence of finite free modules over a linearly ordered
commutative ring, given by an injective linear map `f : A →ₗ[R] B` and a surjective linear map
`g : B →ₗ[R] C` with `Function.Exact f g`, and let `m = dim A` and `n = dim C`. Orientations `o` of
`A` and `p` of `C` induce an orientation `Orientation.ofExact hf hfg hg o p` of `B`, with the
subspace first: for bases `a` of `A` and `c` of `C`, the orientation of `a` and `c` gives the
orientation of the basis `f a₁, …, f aₘ, s₁, …, sₙ` of `B`, where `sⱼ` is any lift of `cⱼ` through
`g` (`Orientation.ofExact_orientation`). This is the orientation form of the determinant-line
identity `det B ≅ det A ⊗ det C` (`TauCeti.detLineShortExactEquiv`), and it does not depend on the
lifts, since two choices of lifts differ by vectors of `range f`, so the change of basis is block
upper triangular with identity diagonal blocks (`Module.Basis.ofExactLift_det_ofExactLift`).

Reversing either orientation reverses the induced one (`Orientation.ofExact_neg_left`,
`Orientation.ofExact_neg_right`), so each of the three orientations is determined by the other
two. This gives the *kernel orientation* `Orientation.kerOfExact` of `A` from orientations of `B`
and `C`, and the *cokernel orientation* `Orientation.cokerOfExact` of `C` from orientations of `A`
and `B`, each characterized by `ofExact` (`Orientation.kerOfExact_eq_iff`,
`Orientation.cokerOfExact_eq_iff`).

The construction is natural: an isomorphism of short exact sequences carries the induced
orientation to the induced orientation of the transported orientations
(`Orientation.map_ofExact`). For the split sequence `A → A × C → C` it is the product orientation
(`Orientation.ofExact_inl_snd`).

This is how trajectory spaces of Morse theory are oriented. At a point `x` of a negative gradient
trajectory from `p` to `q`, with the unstable manifold `W^u(p)` and the stable manifold `W^s(q)`
meeting transversally, the sequence
`0 → T_x (W^u(p) ∩ W^s(q)) → T_x W^u(p) → T_x M ⧸ T_x W^s(q) → 0` is exact. Orientations of
`T_x W^u(p)` and of the normal space `T_x M ⧸ T_x W^s(q)`, which transport along the trajectory
identifies with the tangent space of `W^u(q)` at `q`, then orient `T_x (W^u(p) ∩ W^s(q))` as a
kernel orientation, with the factors in the order `T W^u(p) = T (W^u(p) ∩ W^s(q)) ⊕ T W^u(q)`.
Naturality carries these orientations along the flow.

## Main definitions

* `Orientation.ofExact`: the orientation of the middle term induced by orientations of the outer
  terms, subspace first.
* `Orientation.kerOfExact`: the orientation of the subspace induced by orientations of the middle
  term and of the quotient.
* `Orientation.cokerOfExact`: the orientation of the quotient induced by orientations of the
  subspace and of the middle term.

## Main results

* `Orientation.ofExact_orientation`: the orientation of a basis made of the image of a basis of
  `A` followed by lifts of a basis of `C` is induced by the orientations of these two bases.
* `Orientation.ofExact_neg_left`, `Orientation.ofExact_neg_right`: reversal laws.
* `Orientation.kerOfExact_eq_iff`, `Orientation.cokerOfExact_eq_iff`: the characterizations of
  the kernel and cokernel orientations.
* `Orientation.map_ofExact`: naturality under isomorphisms of short exact sequences.
* `Orientation.ofExact_inl_snd`: for a product, the induced orientation is the product
  orientation.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant lines of exact sequences).
* M. Hutchings, *Lecture notes on Morse homology (with an eye towards Floer theory and
  pseudoholomorphic curves)*, 2002, Section 2 (orientations of the spaces of flow lines).
-/

public section
noncomputable section

open Module

namespace Orientation

variable {R A B C : Type*} [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
  [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
  {f : A →ₗ[R] B} {g : B →ₗ[R] C} {m n : ℕ}
  (hf : Function.Injective f) (hfg : Function.Exact f g) (hg : Function.Surjective g)

omit [LinearOrder R] [IsStrictOrderedRing R] in
/-- The determinant of one reindexed basis of the form `ofExactLift` with respect to another is
the product of the determinants of the bases of the outer terms. -/
private theorem det_reindex_ofExactLift (a a' : Basis (Fin m) R A) (c c' : Basis (Fin n) R C)
    (s s' : Fin n → B) (hs : ∀ j, g (s j) = c j) (hs' : ∀ j, g (s' j) = c' j) :
    ((Basis.ofExactLift hf hfg a c s hs).reindex finSumFinEquiv).det
        ((Basis.ofExactLift hf hfg a' c' s' hs').reindex finSumFinEquiv) =
      a.det a' * c.det c' := by
  rw [Basis.det_reindex]
  have he : ((Basis.ofExactLift hf hfg a' c' s' hs').reindex finSumFinEquiv : Fin (m + n) → B) ∘
      finSumFinEquiv = Basis.ofExactLift hf hfg a' c' s' hs' := by
    funext i
    simp
  rw [he]
  exact Basis.ofExactLift_det_ofExactLift hf hfg a a' c c' s s' hs hs'

/-- The induced orientation of the middle term, computed in chosen bases and lifts. -/
private def ofExactOfBases (o : Orientation R A (Fin m)) (p : Orientation R C (Fin n))
    (a : Basis (Fin m) R A) (c : Basis (Fin n) R C) (s : Fin n → B)
    (hs : ∀ j, g (s j) = c j) : Orientation R B (Fin (m + n)) :=
  rayOfNeZero R (((signBasis o a : R) * (signBasis p c : R)) •
    ((Basis.ofExactLift hf hfg a c s hs).reindex finSumFinEquiv).det) (by
      apply smul_ne_zero
      · exact mul_ne_zero (by exact_mod_cast (signBasis o a).ne_zero)
          (by exact_mod_cast (signBasis p c).ne_zero)
      · exact Basis.det_ne_zero _)

private theorem ofExactOfBases_eq (o : Orientation R A (Fin m)) (p : Orientation R C (Fin n))
    (a a' : Basis (Fin m) R A) (c c' : Basis (Fin n) R C) (s s' : Fin n → B)
    (hs : ∀ j, g (s j) = c j) (hs' : ∀ j, g (s' j) = c' j) :
    ofExactOfBases hf hfg o p a c s hs = ofExactOfBases hf hfg o p a' c' s' hs' := by
  unfold ofExactOfBases
  rw [ray_eq_iff]
  set L := (Basis.ofExactLift hf hfg a c s hs).reindex finSumFinEquiv
  set L' := (Basis.ofExactLift hf hfg a' c' s' hs').reindex finSumFinEquiv
  rw [L.det.eq_smul_basis_det L', smul_smul, det_reindex_ofExactLift]
  apply sameRay_smul_smul_of_mul_nonneg
  have hpos := mul_pos (signBasis_mul_det_mul_pos o a a') (signBasis_mul_det_mul_pos p c c')
  convert hpos.le using 1
  ring

variable [Module.Free R A] [Module.Finite R A] [Module.Free R C] [Module.Finite R C]

/-- The orientation of the middle term `B` of a short exact sequence `0 → A → B → C → 0` induced
by orientations `o` of `A` and `p` of `C`, with the subspace first: a basis of `B` made of the
image of a basis of `A` followed by lifts of a basis of `C` is positive exactly when the two
bases are both positive or both negative (`Orientation.ofExact_orientation`). Both signs of each
factor are retained, including in dimension zero. -/
def ofExact (o : Orientation R A (Fin m)) (p : Orientation R C (Fin n))
    (hm : finrank R A = m) (hn : finrank R C = n) : Orientation R B (Fin (m + n)) :=
  ofExactOfBases hf hfg o p (finBasisOfFinrankEq R A hm) (finBasisOfFinrankEq R C hn)
    (fun j ↦ Function.surjInv hg (finBasisOfFinrankEq R C hn j))
    (fun _ ↦ Function.surjInv_eq hg _)

/-- The induced orientation can be computed in any bases of the outer terms and any lifts, using
their signs relative to the given orientations. -/
private theorem ofExact_eq_ofExactOfBases (o : Orientation R A (Fin m))
    (p : Orientation R C (Fin n)) (hm : finrank R A = m) (hn : finrank R C = n)
    (a : Basis (Fin m) R A) (c : Basis (Fin n) R C) (s : Fin n → B)
    (hs : ∀ j, g (s j) = c j) :
    ofExact hf hfg hg o p hm hn = ofExactOfBases hf hfg o p a c s hs :=
  ofExactOfBases_eq hf hfg o p _ a _ c _ s _ hs

/-- **The orientation of a short exact sequence in bases.** If the first `m` vectors of a basis
`b` of `B` are the image of a basis `a` of `A` and its last `n` vectors lift a basis `c` of `C`,
the orientations of `a` and `c` induce the orientation of `b`. -/
theorem ofExact_orientation (a : Basis (Fin m) R A) (c : Basis (Fin n) R C)
    (b : Basis (Fin (m + n)) R B) (hb : ∀ i, b (Fin.castAdd n i) = f (a i))
    (hb' : ∀ j, g (b (Fin.natAdd m j)) = c j) (hm : finrank R A = m)
    (hn : finrank R C = n) :
    ofExact hf hfg hg a.orientation c.orientation hm hn = b.orientation := by
  rw [Basis.eq_reindex_ofExactLift hf hfg a c b hb hb',
    ofExact_eq_ofExactOfBases hf hfg hg _ _ hm hn a c _ hb']
  simp only [ofExactOfBases, signBasis_orientation, Units.val_one, Int.cast_one, mul_one,
    one_smul]
  -- A basis orientation is by definition the ray of its nonzero determinant form.
  rfl

/-- Reversing the orientation of the subspace reverses the induced orientation. -/
@[simp]
theorem ofExact_neg_left (o : Orientation R A (Fin m)) (p : Orientation R C (Fin n))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    ofExact hf hfg hg (-o) p hm hn = -ofExact hf hfg hg o p hm hn := by
  simp only [ofExact, ofExactOfBases, signBasis_neg, Units.val_neg, Int.cast_neg, neg_mul,
    neg_rayOfNeZero]
  congr 1
  module

/-- Reversing the orientation of the quotient reverses the induced orientation. -/
@[simp]
theorem ofExact_neg_right (o : Orientation R A (Fin m)) (p : Orientation R C (Fin n))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    ofExact hf hfg hg o (-p) hm hn = -ofExact hf hfg hg o p hm hn := by
  simp only [ofExact, ofExactOfBases, signBasis_neg, Units.val_neg, Int.cast_neg, mul_neg,
    neg_rayOfNeZero]
  congr 1
  module

/-- Simultaneous reversal of both outer orientations preserves the induced orientation. -/
theorem ofExact_neg_neg (o : Orientation R A (Fin m)) (p : Orientation R C (Fin n))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    ofExact hf hfg hg (-o) (-p) hm hn = ofExact hf hfg hg o p hm hn := by
  rw [ofExact_neg_left, ofExact_neg_right]
  exact neg_neg (ofExact hf hfg hg o p hm hn)

/-- An orientation of `B` is either the one induced by `o` and `p` or its reverse. -/
theorem eq_ofExact_or_eq_neg_ofExact (q : Orientation R B (Fin (m + n)))
    (o : Orientation R A (Fin m)) (p : Orientation R C (Fin n)) (hm : finrank R A = m)
    (hn : finrank R C = n) :
    q = ofExact hf hfg hg o p hm hn ∨ q = -ofExact hf hfg hg o p hm hn := by
  let a := finBasisOfFinrankEq R A hm
  let c := finBasisOfFinrankEq R C hn
  let s : Fin n → B := fun j ↦ Function.surjInv hg (c j)
  have hs : ∀ j, g (s j) = c j := fun j ↦ Function.surjInv_eq hg _
  let b := (Basis.ofExactLift hf hfg a c s hs).reindex finSumFinEquiv
  have hb : ofExact hf hfg hg a.orientation c.orientation hm hn = b.orientation :=
    ofExact_orientation hf hfg hg a c b (by simp [b]) (by simp [b, hs]) hm hn
  have hnn : ∀ x : Orientation R B (Fin (m + n)), - -x = x := fun x ↦ neg_neg x
  rcases a.orientation_eq_or_eq_neg o with rfl | rfl <;>
    rcases c.orientation_eq_or_eq_neg p with rfl | rfl <;>
    rcases b.orientation_eq_or_eq_neg q with rfl | rfl <;>
    simp [hb, hnn]

/-- The induced orientation determines the orientation of the subspace. -/
theorem ofExact_left_injective (p : Orientation R C (Fin n)) (hm : finrank R A = m)
    (hn : finrank R C = n) :
    Function.Injective fun o : Orientation R A (Fin m) ↦ ofExact hf hfg hg o p hm hn := by
  intro o o' h
  rcases (finBasisOfFinrankEq R A hm).orientation_eq_or_eq_neg o with rfl | rfl <;>
    rcases (finBasisOfFinrankEq R A hm).orientation_eq_or_eq_neg o' with rfl | rfl
  · rfl
  · simp only [ofExact_neg_left] at h
    exact absurd h (Module.Ray.ne_neg_self _)
  · simp only [ofExact_neg_left] at h
    exact absurd h.symm (Module.Ray.ne_neg_self _)
  · rfl

/-- The induced orientation determines the orientation of the quotient. -/
theorem ofExact_right_injective (o : Orientation R A (Fin m)) (hm : finrank R A = m)
    (hn : finrank R C = n) :
    Function.Injective fun p : Orientation R C (Fin n) ↦ ofExact hf hfg hg o p hm hn := by
  intro p p' h
  rcases (finBasisOfFinrankEq R C hn).orientation_eq_or_eq_neg p with rfl | rfl <;>
    rcases (finBasisOfFinrankEq R C hn).orientation_eq_or_eq_neg p' with rfl | rfl
  · rfl
  · simp only [ofExact_neg_right] at h
    exact absurd h (Module.Ray.ne_neg_self _)
  · simp only [ofExact_neg_right] at h
    exact absurd h.symm (Module.Ray.ne_neg_self _)
  · rfl

/-! ### The kernel orientation -/

open Classical in
/-- The **kernel orientation**: the orientation of the subspace `A` of a short exact sequence
`0 → A → B → C → 0` induced by orientations `q` of `B` and `p` of `C`. It is the unique
orientation of `A` that, followed by `p`, induces `q` (`Orientation.kerOfExact_eq_iff`). -/
def kerOfExact (q : Orientation R B (Fin (m + n))) (p : Orientation R C (Fin n))
    (hm : finrank R A = m) (hn : finrank R C = n) : Orientation R A (Fin m) :=
  if ofExact hf hfg hg (finBasisOfFinrankEq R A hm).orientation p hm hn = q then
    (finBasisOfFinrankEq R A hm).orientation
  else -(finBasisOfFinrankEq R A hm).orientation

/-- The kernel orientation followed by `p` induces `q`. -/
@[simp]
theorem ofExact_kerOfExact (q : Orientation R B (Fin (m + n))) (p : Orientation R C (Fin n))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    ofExact hf hfg hg (kerOfExact hf hfg hg q p hm hn) p hm hn = q := by
  unfold kerOfExact
  rcases eq_ofExact_or_eq_neg_ofExact hf hfg hg q (finBasisOfFinrankEq R A hm).orientation p hm
    hn with rfl | rfl
  · rw [ite_eq_left rfl]
  · rw [ite_eq_right (Module.Ray.ne_neg_self
      (ofExact hf hfg hg (finBasisOfFinrankEq R A hm).orientation p hm hn)), ofExact_neg_left]

/-- The kernel orientation of the orientation induced by `o` and `p` is `o`. -/
@[simp]
theorem kerOfExact_ofExact (o : Orientation R A (Fin m)) (p : Orientation R C (Fin n))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    kerOfExact hf hfg hg (ofExact hf hfg hg o p hm hn) p hm hn = o :=
  ofExact_left_injective hf hfg hg p hm hn (ofExact_kerOfExact hf hfg hg _ p hm hn)

/-- **Characterization of the kernel orientation.** -/
theorem kerOfExact_eq_iff (q : Orientation R B (Fin (m + n))) (o : Orientation R A (Fin m))
    (p : Orientation R C (Fin n)) (hm : finrank R A = m) (hn : finrank R C = n) :
    kerOfExact hf hfg hg q p hm hn = o ↔ ofExact hf hfg hg o p hm hn = q := by
  constructor
  · rintro rfl
    exact ofExact_kerOfExact hf hfg hg q p hm hn
  · rintro rfl
    exact kerOfExact_ofExact hf hfg hg o p hm hn

/-- Reversing the orientation of the middle term reverses the kernel orientation. -/
@[simp]
theorem kerOfExact_neg_left (q : Orientation R B (Fin (m + n))) (p : Orientation R C (Fin n))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    kerOfExact hf hfg hg (-q) p hm hn = -kerOfExact hf hfg hg q p hm hn := by
  rw [kerOfExact_eq_iff, ofExact_neg_left, ofExact_kerOfExact]

/-- Reversing the orientation of the quotient reverses the kernel orientation. -/
@[simp]
theorem kerOfExact_neg_right (q : Orientation R B (Fin (m + n))) (p : Orientation R C (Fin n))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    kerOfExact hf hfg hg q (-p) hm hn = -kerOfExact hf hfg hg q p hm hn := by
  rw [kerOfExact_eq_iff, ofExact_neg_neg, ofExact_kerOfExact]

/-! ### The cokernel orientation -/

open Classical in
/-- The **cokernel orientation**: the orientation of the quotient `C` of a short exact sequence
`0 → A → B → C → 0` induced by orientations `o` of `A` and `q` of `B`. It is the unique
orientation of `C` that, preceded by `o`, induces `q` (`Orientation.cokerOfExact_eq_iff`). -/
def cokerOfExact (o : Orientation R A (Fin m)) (q : Orientation R B (Fin (m + n)))
    (hm : finrank R A = m) (hn : finrank R C = n) : Orientation R C (Fin n) :=
  if ofExact hf hfg hg o (finBasisOfFinrankEq R C hn).orientation hm hn = q then
    (finBasisOfFinrankEq R C hn).orientation
  else -(finBasisOfFinrankEq R C hn).orientation

/-- The orientation `o` followed by the cokernel orientation induces `q`. -/
@[simp]
theorem ofExact_cokerOfExact (o : Orientation R A (Fin m)) (q : Orientation R B (Fin (m + n)))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    ofExact hf hfg hg o (cokerOfExact hf hfg hg o q hm hn) hm hn = q := by
  unfold cokerOfExact
  rcases eq_ofExact_or_eq_neg_ofExact hf hfg hg q o (finBasisOfFinrankEq R C hn).orientation hm
    hn with rfl | rfl
  · rw [ite_eq_left rfl]
  · rw [ite_eq_right (Module.Ray.ne_neg_self
      (ofExact hf hfg hg o (finBasisOfFinrankEq R C hn).orientation hm hn)), ofExact_neg_right]

/-- The cokernel orientation of the orientation induced by `o` and `p` is `p`. -/
@[simp]
theorem cokerOfExact_ofExact (o : Orientation R A (Fin m)) (p : Orientation R C (Fin n))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    cokerOfExact hf hfg hg o (ofExact hf hfg hg o p hm hn) hm hn = p :=
  ofExact_right_injective hf hfg hg o hm hn (ofExact_cokerOfExact hf hfg hg o _ hm hn)

/-- **Characterization of the cokernel orientation.** -/
theorem cokerOfExact_eq_iff (o : Orientation R A (Fin m)) (q : Orientation R B (Fin (m + n)))
    (p : Orientation R C (Fin n)) (hm : finrank R A = m) (hn : finrank R C = n) :
    cokerOfExact hf hfg hg o q hm hn = p ↔ ofExact hf hfg hg o p hm hn = q := by
  constructor
  · rintro rfl
    exact ofExact_cokerOfExact hf hfg hg o q hm hn
  · rintro rfl
    exact cokerOfExact_ofExact hf hfg hg o p hm hn

/-- Reversing the orientation of the subspace reverses the cokernel orientation. -/
@[simp]
theorem cokerOfExact_neg_left (o : Orientation R A (Fin m)) (q : Orientation R B (Fin (m + n)))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    cokerOfExact hf hfg hg (-o) q hm hn = -cokerOfExact hf hfg hg o q hm hn := by
  rw [cokerOfExact_eq_iff, ofExact_neg_neg, ofExact_cokerOfExact]

/-- Reversing the orientation of the middle term reverses the cokernel orientation. -/
@[simp]
theorem cokerOfExact_neg_right (o : Orientation R A (Fin m)) (q : Orientation R B (Fin (m + n)))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    cokerOfExact hf hfg hg o (-q) hm hn = -cokerOfExact hf hfg hg o q hm hn := by
  rw [cokerOfExact_eq_iff, ofExact_neg_right, ofExact_cokerOfExact]

/-! ### Naturality and products -/

section Map

variable {A' B' C' : Type*} [AddCommGroup A'] [Module R A'] [AddCommGroup B'] [Module R B']
  [AddCommGroup C'] [Module R C'] [Module.Free R A'] [Module.Finite R A'] [Module.Free R C']
  [Module.Finite R C'] {f' : A' →ₗ[R] B'} {g' : B' →ₗ[R] C'}
  (hf' : Function.Injective f') (hfg' : Function.Exact f' g') (hg' : Function.Surjective g')

/-- **Naturality of the induced orientation.** An isomorphism of short exact sequences, given by
linear equivalences `eA`, `eB`, `eC` of the three terms commuting with the maps, carries the
orientation induced by `o` and `p` to the orientation induced by their transports. -/
theorem map_ofExact (eA : A ≃ₗ[R] A') (eB : B ≃ₗ[R] B') (eC : C ≃ₗ[R] C')
    (hfe : ∀ x, eB (f x) = f' (eA x)) (hge : ∀ y, eC (g y) = g' (eB y))
    (o : Orientation R A (Fin m)) (p : Orientation R C (Fin n)) (hm : finrank R A = m)
    (hn : finrank R C = n) :
    Orientation.map (Fin (m + n)) eB (ofExact hf hfg hg o p hm hn) =
      ofExact hf' hfg' hg' (Orientation.map (Fin m) eA o) (Orientation.map (Fin n) eC p)
        (eA.finrank_eq.symm.trans hm) (eC.finrank_eq.symm.trans hn) := by
  let a := finBasisOfFinrankEq R A hm
  let c := finBasisOfFinrankEq R C hn
  let s : Fin n → B := fun j ↦ Function.surjInv hg (c j)
  have hs : ∀ j, g (s j) = c j := fun j ↦ Function.surjInv_eq hg _
  let b := (Basis.ofExactLift hf hfg a c s hs).reindex finSumFinEquiv
  have hbase : Orientation.map (Fin (m + n)) eB (ofExact hf hfg hg a.orientation c.orientation
      hm hn) = ofExact hf' hfg' hg' (Orientation.map (Fin m) eA a.orientation)
        (Orientation.map (Fin n) eC c.orientation) (eA.finrank_eq.symm.trans hm)
        (eC.finrank_eq.symm.trans hn) := by
    rw [ofExact_orientation hf hfg hg a c b (by simp [b]) (by simp [b, hs]) hm hn,
      ← Basis.orientation_map, ← Basis.orientation_map, ← Basis.orientation_map]
    refine (ofExact_orientation hf' hfg' hg' (a.map eA) (c.map eC) (b.map eB) (fun i ↦ ?_)
      (fun j ↦ ?_) _ _).symm
    · simp [b, hfe]
    · simp [b, ← hge, hs]
  rcases a.orientation_eq_or_eq_neg o with rfl | rfl <;>
    rcases c.orientation_eq_or_eq_neg p with rfl | rfl <;>
    simp only [ofExact_neg_left, ofExact_neg_right, Orientation.map_neg, hbase]

end Map

/-- For the split exact sequence `A → A × C → C`, the induced orientation is the product
orientation. -/
theorem ofExact_inl_snd (o : Orientation R A (Fin m)) (p : Orientation R C (Fin n))
    (hm : finrank R A = m) (hn : finrank R C = n) :
    ofExact (LinearMap.inl_injective (R := R) (M := A) (M₂ := C)) Function.Exact.inl_snd
      LinearMap.snd_surjective o p hm hn = prod o p hm hn := by
  let a := finBasisOfFinrankEq R A hm
  let c := finBasisOfFinrankEq R C hn
  have hbase : ofExact (LinearMap.inl_injective (R := R) (M := A) (M₂ := C))
      Function.Exact.inl_snd LinearMap.snd_surjective a.orientation c.orientation hm hn =
      prod a.orientation c.orientation hm hn := by
    rw [prod_basis_orientation]
    exact ofExact_orientation _ _ _ a c _ (fun i ↦ by simp [Basis.prod_apply])
      (fun j ↦ by simp [Basis.prod_apply]) hm hn
  rcases a.orientation_eq_or_eq_neg o with rfl | rfl <;>
    rcases c.orientation_eq_or_eq_neg p with rfl | rfl <;>
    simp only [ofExact_neg_left, ofExact_neg_right, prod_neg_left, prod_neg_right, hbase]

end Orientation

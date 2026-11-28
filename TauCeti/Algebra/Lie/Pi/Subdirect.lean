/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Pi
public import Mathlib.Algebra.Lie.Semisimple.Basic

/-!
# Pairwise surjective Lie subalgebras of finite products

A Lie subalgebra of a finite product of perfect Lie algebras is the whole product if it
surjects onto each coordinate and each pair of distinct coordinates. The single-coordinate
hypothesis covers a product with just one factor. For two or more factors it follows from
pairwise surjectivity.

The simple-factor case is the Lie algebra form of Ribet's lemma used by Lawrence and
Venkatesh in *Diophantine problems and p-adic period mappings*, §2.7, preceding Lemma 2.12.
-/

public section

namespace LieSubalgebra

variable {ι R : Type*} {L : ι → Type*} [CommRing R] [∀ i, LieRing (L i)]
  [∀ i, LieAlgebra R (L i)]

/-- At a perfect coordinate, constraints that can individually be made zero while preserving
projection onto that coordinate can also be made zero simultaneously on a finite set. -/
theorem exists_apply_eq_and_forall_apply_eq_zero (S : LieSubalgebra R (∀ i, L i))
    (i : ι) (t : Finset ι) (hperf : LieAlgebra.derivedSeries R (L i) 1 = ⊤)
    (hproj : Function.Surjective (fun x : S => x.val i))
    (hlift : ∀ j ∈ t, ∀ a : L i, ∃ x : S, x.val i = a ∧ x.val j = 0)
    (a : L i) : ∃ x : S, x.val i = a ∧ ∀ j ∈ t, x.val j = 0 := by
  classical
  let p (j : ι) := (LieHom.proj (R := R) (L := L) j).comp S.incl
  have heval (j) : ⇑(p j) = fun x : S => x.val j := funext fun x => LieHom.proj_apply j x.val
  have hsurj : Function.Surjective (p i) := heval i ▸ hproj
  let K (j : ι) := (p j).ker
  have hmeet : (t.inf K).map (p i) = ⊤ := by
    induction t using Finset.induction_on with
    | empty => rw [Finset.inf_empty, ← LieHom.idealRange_eq_map,
        (p i).idealRange_eq_top_of_surjective hsurj]
    | @insert j t _ ih =>
      have hk : (K j).map (p i) = ⊤ := by
        apply _root_.eq_top_iff.mpr
        intro b _
        obtain ⟨x, hx, hz⟩ := hlift j (Finset.mem_insert_self ..) b
        have hxi : p i x = b := by simpa only [heval] using hx
        rw [← hxi]
        exact LieIdeal.mem_map ((p j).mem_ker.mpr (by simpa only [heval] using hz))
      have hrec := ih (fun k hkt => hlift k (Finset.mem_insert_of_mem hkt))
      have hle := LieIdeal.map_mono (f := p i) (LieSubmodule.lie_le_inf (K j) (t.inf K))
      rw [LieIdeal.map_bracket_eq _ hsurj, hk, hrec] at hle
      rw [Finset.inf_insert]
      exact top_unique (hperf ▸ hle)
  obtain ⟨x, hxa⟩ := LieIdeal.mem_map_of_surjective (f := p i) hsurj
    (hmeet ▸ LieSubmodule.mem_top a : a ∈ (t.inf K).map (p i))
  refine ⟨x.val, by simpa only [heval] using hxa, fun j hj => ?_⟩
  have hk : x.val ∈ K j := (Finset.inf_le (f := K) hj) x.property
  simpa only [heval] using (p j).mem_ker.mp hk

/-- A Lie subalgebra of a finite product of perfect Lie algebras is the whole product if the
individual coordinate projections and all projections onto pairs of distinct coordinates are
surjective. -/
theorem eq_top_of_pairwise_surjective_of_perfect [Finite ι]
    (S : LieSubalgebra R (∀ i, L i)) (hperf : ∀ i, LieAlgebra.derivedSeries R (L i) 1 = ⊤)
    (hproj : ∀ i, Function.Surjective (fun x : S => x.val i))
    (hpair : Pairwise (fun i j => Function.Surjective (fun x : S => (x.val i, x.val j)))) :
    S = ⊤ := by
  classical
  let := Fintype.ofFinite ι
  apply eq_top_iff.mpr
  intro x _
  rw [← Finset.univ_sum_single x]
  apply S.sum_mem
  intro i _
  obtain ⟨z, hzi, hz⟩ := S.exists_apply_eq_and_forall_apply_eq_zero i (Finset.univ.erase i)
    (hperf i) (hproj i) (fun j hj a => by
      obtain ⟨u, hu⟩ := hpair (Finset.ne_of_mem_erase hj).symm (a, 0)
      exact ⟨u, congrArg Prod.fst hu, congrArg Prod.snd hu⟩) (x i)
  have heq : z.val = Pi.single i (x i) := by
    ext j
    by_cases hji : j = i
    · subst j; simpa only [Pi.single_eq_same] using hzi
    · rw [Pi.single_eq_of_ne hji]
      exact hz j (Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩)
  exact heq ▸ z.property

/-- **Ribet's lemma for simple Lie algebras**. A subalgebra projecting onto each factor and each
pair of distinct factors of a finite product of nonabelian simple Lie algebras is the
full product. -/
theorem eq_top_of_pairwise_surjective_of_isSimple [Finite ι] [∀ i, LieAlgebra.IsSimple R (L i)]
    (S : LieSubalgebra R (∀ i, L i))
    (hproj : ∀ i, Function.Surjective (fun x : S => x.val i))
    (hpair : Pairwise (fun i j => Function.Surjective (fun x : S => (x.val i, x.val j)))) :
    S = ⊤ := by
  apply S.eq_top_of_pairwise_surjective_of_perfect _ hproj hpair
  intro i
  have h := LieAlgebra.IsSimple.isAtom_top R (L i)
  exact lie_eq_self_of_isAtom_of_nonabelian _ h (LieAlgebra.IsSemisimple.non_abelian_of_isAtom _ h)

end LieSubalgebra

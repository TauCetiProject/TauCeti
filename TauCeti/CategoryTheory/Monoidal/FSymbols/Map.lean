/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Monoidal.FSymbols.Basic

/-!
# Relabeling and base change for F-symbols and R-symbols

This file constructs relabeling (`reindex`) along unit- and multiplicity-preserving bijections of
the simple-object index set and base change (`map`) along ring homomorphisms for
`TauCeti.FusionRules`, `TauCeti.FSymbols`, and `TauCeti.RSymbols`.

Because the pentagon, triangle, hexagon, and two-sided matrix inverse conditions are polynomial
identities in the matrix entries, entrywise application of any ring homomorphism `f : R →+* S`
transports F-symbols and R-symbols from `R` to `S`. Likewise, any bijection `σ : ι ≃ ι'`
intertwining the distinguished unit and fusion multiplicities transports F-symbols and R-symbols
covariantly, satisfying `reindex (Equiv.refl ι) = id`,
`reindex (σ.trans τ) = reindex τ ∘ reindex σ`, `map (RingHom.id R) = id`,
`map (g.comp f) = map g ∘ map f`, and commutativity of `reindex` with `map`.

## References

* [P. Etingof, S. Gelaki, D. Nikshych, V. Ostrik, *Tensor Categories*][egno15], §4.9–4.10.
* A. Kitaev, *Anyons in an exactly solved model and beyond*, Ann. Physics **321** (2006),
  Appendix E, §E.1 and §E.3.
-/

public section

namespace TauCeti

universe u u' u'' v v' v''

/-! ### Relabeling of fusion rules -/

namespace FusionRules

section Reindex

variable {ι : Type u} {ι' : Type u'} {ι'' : Type u''}
  [DecidableEq ι] [DecidableEq ι'] [DecidableEq ι'']

/-- Push `FusionRules` forward along a bijection `σ : ι ≃ ι'`. -/
def reindex (σ : ι ≃ ι') (N : FusionRules ι) : FusionRules ι' where
  unit := σ N.unit
  N a' b' c' := N.N (σ.symm a') (σ.symm b') (σ.symm c')
  N_unit_left a' b' := by simp [N.N_unit_left, σ.symm.injective.eq_iff]
  N_unit_right a' b' := by simp [N.N_unit_right, σ.symm.injective.eq_iff]

@[simp]
theorem reindex_unit (σ : ι ≃ ι') (N : FusionRules ι) :
    (N.reindex σ).unit = σ N.unit :=
  (rfl)

@[simp]
theorem reindex_N_apply (σ : ι ≃ ι') (N : FusionRules ι) (a' b' c' : ι') :
    (N.reindex σ).N a' b' c' = N.N (σ.symm a') (σ.symm b') (σ.symm c') :=
  (rfl)

theorem N_eq_reindex_N (σ : ι ≃ ι') (N : FusionRules ι) (a b c : ι) :
    N.N a b c = (N.reindex σ).N (σ a) (σ b) (σ c) := by
  simp

@[simp]
theorem reindex_refl_apply (N : FusionRules ι) : N.reindex (Equiv.refl ι) = N := by
  ext <;> rfl

theorem reindex_refl :
    (FusionRules.reindex (Equiv.refl ι) : FusionRules ι → FusionRules ι) = id :=
  funext reindex_refl_apply

@[simp]
theorem reindex_trans_apply (σ : ι ≃ ι') (τ : ι' ≃ ι'') (N : FusionRules ι) :
    (N.reindex σ).reindex τ = N.reindex (σ.trans τ) := by
  ext <;> rfl

theorem reindex_trans (σ : ι ≃ ι') (τ : ι' ≃ ι'') :
    (FusionRules.reindex (σ.trans τ) : FusionRules ι → FusionRules ι'') =
      FusionRules.reindex τ ∘ FusionRules.reindex σ :=
  funext fun N ↦ (reindex_trans_apply σ τ N).symm

/-- `FusionRules.reindex` along a bijection `σ : ι ≃ ι'` as an equivalence of types. -/
def reindexEquiv (σ : ι ≃ ι') : FusionRules ι ≃ FusionRules ι' where
  toFun := reindex σ
  invFun := reindex σ.symm
  left_inv N := by simp
  right_inv N' := by simp

@[simp]
theorem reindexEquiv_apply (σ : ι ≃ ι') (N : FusionRules ι) :
    reindexEquiv σ N = N.reindex σ :=
  (rfl)

@[simp]
theorem reindexEquiv_symm (σ : ι ≃ ι') :
    (reindexEquiv σ).symm = reindexEquiv σ.symm :=
  (rfl)

/-! #### Composite index equivalences along multiplicity-preserving bijections -/

section IndexEquiv

variable {N : FusionRules ι} {N' : FusionRules ι'}

theorem N_symm_eq (σ : ι ≃ ι') (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c))
    (a' b' c' : ι') :
    N'.N a' b' c' = N.N (σ.symm a') (σ.symm b') (σ.symm c') := by
  simpa using (hN (σ.symm a') (σ.symm b') (σ.symm c')).symm

theorem Left.ext_val {a b c d e₁ e₂ : ι}
    {i₁ : Fin (N.N a b e₁)} {i₂ : Fin (N.N a b e₂)}
    {j₁ : Fin (N.N e₁ c d)} {j₂ : Fin (N.N e₂ c d)}
    (he : e₁ = e₂) (hi : i₁.val = i₂.val) (hj : j₁.val = j₂.val) :
    (⟨e₁, i₁, j₁⟩ : N.Left a b c d) = ⟨e₂, i₂, j₂⟩ := by
  subst he
  rw [Fin.ext hi, Fin.ext hj]

theorem Right.ext_val {a b c d f₁ f₂ : ι}
    {k₁ : Fin (N.N b c f₁)} {k₂ : Fin (N.N b c f₂)}
    {l₁ : Fin (N.N a f₁ d)} {l₂ : Fin (N.N a f₂ d)}
    (hf : f₁ = f₂) (hk : k₁.val = k₂.val) (hl : l₁.val = l₂.val) :
    (⟨f₁, k₁, l₁⟩ : N.Right a b c d) = ⟨f₂, k₂, l₂⟩ := by
  subst hf
  rw [Fin.ext hk, Fin.ext hl]

variable (σ : ι ≃ ι') (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c))

/-- Equivalence between `N'.Left a' b' c' d'` and the preimage composite index type
`N.Left (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')`. -/
def leftSymmEquiv (a' b' c' d' : ι') :
    N'.Left a' b' c' d' ≃ N.Left (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d') :=
  Equiv.sigmaCongr σ.symm fun e' ↦
    (finCongr (N_symm_eq σ hN a' b' e')).prodCongr (finCongr (N_symm_eq σ hN e' c' d'))

@[simp]
theorem leftSymmEquiv_apply (a' b' c' d' : ι') (x : N'.Left a' b' c' d') :
    leftSymmEquiv σ hN a' b' c' d' x =
      ⟨σ.symm x.1,
        x.2.1.cast (N_symm_eq σ hN a' b' x.1),
        x.2.2.cast (N_symm_eq σ hN x.1 c' d')⟩ := by
  rcases x with ⟨_, _, _⟩
  simp [leftSymmEquiv, Equiv.sigmaCongr]

@[simp]
theorem leftSymmEquiv_symm_apply (a' b' c' d' : ι')
    (x : N.Left (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')) :
    (leftSymmEquiv σ hN a' b' c' d').symm x =
      ⟨σ x.1,
        x.2.1.cast (by simp [N_symm_eq σ hN]),
        x.2.2.cast (by simp [N_symm_eq σ hN])⟩ := by
  rcases x with ⟨e, i, j⟩
  apply (leftSymmEquiv σ hN a' b' c' d').symm_apply_eq.mpr
  rw [leftSymmEquiv_apply]
  exact Left.ext_val (by simp) rfl rfl

/-- Equivalence between `N'.Right a' b' c' d'` and the preimage composite index type
`N.Right (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')`. -/
def rightSymmEquiv (a' b' c' d' : ι') :
    N'.Right a' b' c' d' ≃ N.Right (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d') :=
  Equiv.sigmaCongr σ.symm fun f' ↦
    (finCongr (N_symm_eq σ hN b' c' f')).prodCongr (finCongr (N_symm_eq σ hN a' f' d'))

@[simp]
theorem rightSymmEquiv_apply (a' b' c' d' : ι') (y : N'.Right a' b' c' d') :
    rightSymmEquiv σ hN a' b' c' d' y =
      ⟨σ.symm y.1,
        y.2.1.cast (N_symm_eq σ hN b' c' y.1),
        y.2.2.cast (N_symm_eq σ hN a' y.1 d')⟩ := by
  rcases y with ⟨_, _, _⟩
  simp [rightSymmEquiv, Equiv.sigmaCongr]

@[simp]
theorem rightSymmEquiv_symm_apply (a' b' c' d' : ι')
    (y : N.Right (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')) :
    (rightSymmEquiv σ hN a' b' c' d').symm y =
      ⟨σ y.1,
        y.2.1.cast (by simp [N_symm_eq σ hN]),
        y.2.2.cast (by simp [N_symm_eq σ hN])⟩ := by
  rcases y with ⟨f, k, l⟩
  apply (rightSymmEquiv σ hN a' b' c' d').symm_apply_eq.mpr
  rw [rightSymmEquiv_apply]
  exact Right.ext_val (by simp) rfl rfl

end IndexEquiv

end Reindex

end FusionRules

/-! ### Relabeling and base change for F-symbols -/

namespace FSymbols

section ReindexAndMap

variable {R : Type v} {S : Type v'} {T : Type v''} [CommRing R] [CommRing S] [CommRing T]
  {ι : Type u} {ι' : Type u'} {ι'' : Type u''}
  [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype ι''] [DecidableEq ι'']
  {N : FusionRules ι} {N' : FusionRules ι'} {N'' : FusionRules ι''}

private theorem triangle_of_eq_unit (P : FSymbols R N) {u₀ : ι} (hu : u₀ = N.unit)
    (a c d : ι) (ua : Fin (N.N a u₀ a)) (uc : Fin (N.N u₀ c c)) (i j : Fin (N.N a c d)) :
    P.F a u₀ c d ⟨a, ua, i⟩ ⟨c, uc, j⟩ = if i = j then 1 else 0 := by
  subst hu
  rw [N.fin_unit_right_eq a ua, N.fin_unit_left_eq c uc]
  exact P.triangle a c d i j

private theorem F_cast_of_eq (P : FSymbols R N)
    {a₁ a b₁ b c₁ c d₁ d e₁ e f₁ f : ι}
    (ha : a₁ = a) (hb : b₁ = b) (hc : c₁ = c) (hd : d₁ = d) (he : e₁ = e) (hf : f₁ = f)
    {i₁ : Fin (N.N a₁ b₁ e₁)} {i : Fin (N.N a b e)} (hi : i₁.val = i.val)
    {j₁ : Fin (N.N e₁ c₁ d₁)} {j : Fin (N.N e c d)} (hj : j₁.val = j.val)
    {k₁ : Fin (N.N b₁ c₁ f₁)} {k : Fin (N.N b c f)} (hk : k₁.val = k.val)
    {l₁ : Fin (N.N a₁ f₁ d₁)} {l : Fin (N.N a f d)} (hl : l₁.val = l.val) :
    P.F a₁ b₁ c₁ d₁ ⟨e₁, i₁, j₁⟩ ⟨f₁, k₁, l₁⟩ =
      P.F a b c d ⟨e, i, j⟩ ⟨f, k, l⟩ := by
  subst ha; subst hb; subst hc; subst hd; subst he; subst hf
  rw [Fin.ext hi, Fin.ext hj, Fin.ext hk, Fin.ext hl]

/-- Transport `FSymbols` covariantly along a unit- and multiplicity-preserving bijection
`σ : ι ≃ ι'`. -/
def reindex (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols R N) : FSymbols R N' where
  F a' b' c' d' :=
    (P.F (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')).submatrix
      (FusionRules.leftSymmEquiv σ hN a' b' c' d')
      (FusionRules.rightSymmEquiv σ hN a' b' c' d')
  Finv a' b' c' d' :=
    (P.Finv (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')).submatrix
      (FusionRules.rightSymmEquiv σ hN a' b' c' d')
      (FusionRules.leftSymmEquiv σ hN a' b' c' d')
  F_mul_Finv a' b' c' d' := by
    rw [Matrix.submatrix_mul_equiv, P.F_mul_Finv, Matrix.submatrix_one_equiv]
  Finv_mul_F a' b' c' d' := by
    rw [Matrix.submatrix_mul_equiv, P.Finv_mul_F, Matrix.submatrix_one_equiv]
  pentagon A' B' C' D' E' p' q' r' s' i₁' i₂' i₃' k' m' n' := by
    refine Eq.trans ?_ ((P.pentagon
      (σ.symm A') (σ.symm B') (σ.symm C') (σ.symm D') (σ.symm E')
      (σ.symm p') (σ.symm q') (σ.symm r') (σ.symm s')
      (i₁'.cast (FusionRules.N_symm_eq σ hN A' B' p'))
      (i₂'.cast (FusionRules.N_symm_eq σ hN p' C' q'))
      (i₃'.cast (FusionRules.N_symm_eq σ hN q' D' E'))
      (k'.cast (FusionRules.N_symm_eq σ hN C' D' r'))
      (m'.cast (FusionRules.N_symm_eq σ hN B' r' s'))
      (n'.cast (FusionRules.N_symm_eq σ hN A' s' E'))).trans (Eq.symm ?_))
    · exact Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN p' r' E')) _ _
        fun _ ↦ by simp
    · exact Fintype.sum_equiv σ.symm _ _ fun t' ↦
        Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN B' C' t')) _ _ fun _ ↦
          Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN A' t' q')) _ _ fun _ ↦
            Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN t' D' s')) _ _
              fun _ ↦ by simp
  triangle a' c' d' i' j' := by
    have hu : σ.symm N'.unit = N.unit := by rw [← hunit, σ.symm_apply_apply]
    simpa [Fin.ext_iff] using
      P.triangle_of_eq_unit hu (σ.symm a') (σ.symm c') (σ.symm d')
        ((N'.unitRight a').cast (FusionRules.N_symm_eq σ hN a' N'.unit a'))
        ((N'.unitLeft c').cast (FusionRules.N_symm_eq σ hN N'.unit c' c'))
        (i'.cast (FusionRules.N_symm_eq σ hN a' c' d'))
        (j'.cast (FusionRules.N_symm_eq σ hN a' c' d'))

@[simp]
theorem reindex_F_apply (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols R N)
    (a' b' c' d' : ι') (x : N'.Left a' b' c' d') (y : N'.Right a' b' c' d') :
    (P.reindex σ hunit hN).F a' b' c' d' x y =
      P.F (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')
        (FusionRules.leftSymmEquiv σ hN a' b' c' d' x)
        (FusionRules.rightSymmEquiv σ hN a' b' c' d' y) :=
  (rfl)

@[simp]
theorem reindex_Finv_apply (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols R N)
    (a' b' c' d' : ι') (y : N'.Right a' b' c' d') (x : N'.Left a' b' c' d') :
    (P.reindex σ hunit hN).Finv a' b' c' d' y x =
      P.Finv (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d')
        (FusionRules.rightSymmEquiv σ hN a' b' c' d' y)
        (FusionRules.leftSymmEquiv σ hN a' b' c' d' x) :=
  (rfl)

@[simp]
theorem reindex_refl_apply (hunit : Equiv.refl ι N.unit = N.unit)
    (hN : ∀ a b c, N.N a b c = N.N (Equiv.refl ι a) (Equiv.refl ι b) (Equiv.refl ι c))
    (P : FSymbols R N) :
    P.reindex (Equiv.refl ι) hunit hN = P := by
  ext a b c d ⟨e, i, j⟩ ⟨f, k, l⟩
  rw [reindex_F_apply, FusionRules.leftSymmEquiv_apply, FusionRules.rightSymmEquiv_apply]
  refine F_cast_of_eq P rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ <;> rfl

theorem reindex_refl (hunit : Equiv.refl ι N.unit = N.unit)
    (hN : ∀ a b c, N.N a b c = N.N (Equiv.refl ι a) (Equiv.refl ι b) (Equiv.refl ι c)) :
    (FSymbols.reindex (Equiv.refl ι) hunit hN : FSymbols R N → FSymbols R N) = id :=
  funext (reindex_refl_apply hunit hN)

@[simp]
theorem reindex_trans_apply (σ : ι ≃ ι') (τ : ι' ≃ ι'')
    (hunit₁ : σ N.unit = N'.unit)
    (hN₁ : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c))
    (hunit₂ : τ N'.unit = N''.unit)
    (hN₂ : ∀ a' b' c', N'.N a' b' c' = N''.N (τ a') (τ b') (τ c'))
    (P : FSymbols R N) :
    (P.reindex σ hunit₁ hN₁).reindex τ hunit₂ hN₂ =
      P.reindex (σ.trans τ) (by simp [hunit₁, hunit₂]) (by simp [hN₁, hN₂]) := by
  ext a'' b'' c'' d'' ⟨e'', i'', j''⟩ ⟨f'', k'', l''⟩
  rw [reindex_F_apply, reindex_F_apply, reindex_F_apply,
    FusionRules.leftSymmEquiv_apply, FusionRules.rightSymmEquiv_apply,
    FusionRules.leftSymmEquiv_apply, FusionRules.rightSymmEquiv_apply,
    FusionRules.leftSymmEquiv_apply, FusionRules.rightSymmEquiv_apply]
  refine F_cast_of_eq P rfl rfl rfl rfl rfl rfl ?_ ?_ ?_ ?_ <;> rfl

theorem reindex_trans (σ : ι ≃ ι') (τ : ι' ≃ ι'')
    (hunit₁ : σ N.unit = N'.unit)
    (hN₁ : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c))
    (hunit₂ : τ N'.unit = N''.unit)
    (hN₂ : ∀ a' b' c', N'.N a' b' c' = N''.N (τ a') (τ b') (τ c'))
    (hunit₁₂ : (σ.trans τ) N.unit = N''.unit)
    (hN₁₂ : ∀ a b c, N.N a b c =
      N''.N ((σ.trans τ) a) ((σ.trans τ) b) ((σ.trans τ) c)) :
    (FSymbols.reindex (σ.trans τ) hunit₁₂ hN₁₂ : FSymbols R N → FSymbols R N'') =
      FSymbols.reindex τ hunit₂ hN₂ ∘ FSymbols.reindex σ hunit₁ hN₁ :=
  funext fun P ↦ (reindex_trans_apply σ τ hunit₁ hN₁ hunit₂ hN₂ P).symm

/-- `FSymbols.reindex` along a unit- and multiplicity-preserving bijection as an equivalence. -/
def reindexEquiv (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) :
    FSymbols R N ≃ FSymbols R N' where
  toFun := reindex σ hunit hN
  invFun := reindex σ.symm (by rw [← hunit, σ.symm_apply_apply])
    (FusionRules.N_symm_eq σ hN)
  left_inv P := by
    ext a b c d ⟨e, i, j⟩ ⟨f, k, l⟩
    rw [reindex_F_apply, reindex_F_apply,
      FusionRules.leftSymmEquiv_apply, FusionRules.rightSymmEquiv_apply,
      FusionRules.leftSymmEquiv_apply, FusionRules.rightSymmEquiv_apply]
    refine F_cast_of_eq P (σ.symm_apply_apply a) (σ.symm_apply_apply b)
      (σ.symm_apply_apply c) (σ.symm_apply_apply d) (σ.symm_apply_apply e)
      (σ.symm_apply_apply f) ?_ ?_ ?_ ?_ <;> rfl
  right_inv P' := by
    ext a' b' c' d' ⟨e', i', j'⟩ ⟨f', k', l'⟩
    rw [reindex_F_apply, reindex_F_apply,
      FusionRules.leftSymmEquiv_apply, FusionRules.rightSymmEquiv_apply,
      FusionRules.leftSymmEquiv_apply, FusionRules.rightSymmEquiv_apply]
    refine F_cast_of_eq P' (σ.apply_symm_apply a') (σ.apply_symm_apply b')
      (σ.apply_symm_apply c') (σ.apply_symm_apply d') (σ.apply_symm_apply e')
      (σ.apply_symm_apply f') ?_ ?_ ?_ ?_ <;> rfl

@[simp]
theorem reindexEquiv_apply (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols R N) :
    reindexEquiv σ hunit hN P = P.reindex σ hunit hN :=
  (rfl)

@[simp]
theorem reindexEquiv_symm_apply (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P' : FSymbols R N') :
    (reindexEquiv σ hunit hN).symm P' =
      P'.reindex σ.symm (by rw [← hunit, σ.symm_apply_apply])
        (FusionRules.N_symm_eq σ hN) :=
  (rfl)

/-- Base change of `FSymbols` along a ring homomorphism `f : R →+* S`, applying `f` entrywise to
`F` and `Finv`. -/
def map (f : R →+* S) (P : FSymbols R N) : FSymbols S N where
  F a b c d := (P.F a b c d).map f
  Finv a b c d := (P.Finv a b c d).map f
  F_mul_Finv a b c d := by
    rw [← Matrix.map_mul, P.F_mul_Finv, Matrix.map_one f (map_zero f) (map_one f)]
  Finv_mul_F a b c d := by
    rw [← Matrix.map_mul, P.Finv_mul_F, Matrix.map_one f (map_zero f) (map_one f)]
  pentagon A B C D E p q r s i₁ i₂ i₃ k m n := by
    simpa [Matrix.map_apply, map_sum, map_mul] using
      congrArg f (P.pentagon A B C D E p q r s i₁ i₂ i₃ k m n)
  triangle a c d j l := by
    split_ifs with h <;> simp [P.triangle, h]

@[simp]
theorem map_F_apply (f : R →+* S) (P : FSymbols R N) (a b c d : ι)
    (x : N.Left a b c d) (y : N.Right a b c d) :
    (P.map f).F a b c d x y = f (P.F a b c d x y) :=
  (rfl)

@[simp]
theorem map_Finv_apply (f : R →+* S) (P : FSymbols R N) (a b c d : ι)
    (y : N.Right a b c d) (x : N.Left a b c d) :
    (P.map f).Finv a b c d y x = f (P.Finv a b c d y x) :=
  (rfl)

theorem map_F (f : R →+* S) (P : FSymbols R N) (a b c d : ι) :
    (P.map f).F a b c d = (P.F a b c d).map f :=
  (rfl)

theorem map_Finv (f : R →+* S) (P : FSymbols R N) (a b c d : ι) :
    (P.map f).Finv a b c d = (P.Finv a b c d).map f :=
  (rfl)

@[simp]
theorem map_id_apply (P : FSymbols R N) : P.map (RingHom.id R) = P := by
  ext a b c d x y
  simp

theorem map_id : (FSymbols.map (RingHom.id R) : FSymbols R N → FSymbols R N) = id :=
  funext map_id_apply

@[simp]
theorem map_comp_apply (f : R →+* S) (g : S →+* T) (P : FSymbols R N) :
    (P.map f).map g = P.map (g.comp f) := by
  ext a b c d x y
  simp

theorem map_comp (f : R →+* S) (g : S →+* T) :
    (FSymbols.map (g.comp f) : FSymbols R N → FSymbols T N) = FSymbols.map g ∘ FSymbols.map f :=
  funext fun P ↦ (map_comp_apply f g P).symm

/-- Base change of `FSymbols` along a ring isomorphism `e : R ≃+* S` as an equivalence. -/
def mapRingEquiv (e : R ≃+* S) : FSymbols R N ≃ FSymbols S N where
  toFun := map (e : R →+* S)
  invFun := map (e.symm : S →+* R)
  left_inv P := by simp
  right_inv P' := by simp

@[simp]
theorem mapRingEquiv_apply (e : R ≃+* S) (P : FSymbols R N) :
    mapRingEquiv e P = P.map (e : R →+* S) :=
  (rfl)

@[simp]
theorem mapRingEquiv_symm (e : R ≃+* S) :
    (mapRingEquiv e : FSymbols R N ≃ FSymbols S N).symm = mapRingEquiv e.symm :=
  (rfl)

/-- `FSymbols.reindex` and `FSymbols.map` commute. -/
theorem reindex_map_apply (f : R →+* S) (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols R N) :
    (P.map f).reindex σ hunit hN = (P.reindex σ hunit hN).map f := by
  ext a' b' c' d' x y
  simp

theorem reindex_comp_map (f : R →+* S) (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) :
    (FSymbols.reindex σ hunit hN ∘ FSymbols.map f : FSymbols R N → FSymbols S N') =
      FSymbols.map f ∘ FSymbols.reindex σ hunit hN :=
  funext (reindex_map_apply f σ hunit hN)

end ReindexAndMap

end FSymbols

/-! ### Relabeling and base change for R-symbols -/

namespace RSymbols

section ReindexAndMap

variable {K : Type v} {L : Type v'} {M : Type v''} [CommRing K] [CommRing L] [CommRing M]
  {ι : Type u} {ι' : Type u'} {ι'' : Type u''}
  [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι'] [Fintype ι''] [DecidableEq ι'']
  {N : FusionRules ι} {N' : FusionRules ι'} {N'' : FusionRules ι''}

private theorem R_cast_of_eq {P : FSymbols K N} (Q : RSymbols P)
    {a₁ a b₁ b c₁ c : ι} (ha : a₁ = a) (hb : b₁ = b) (hc : c₁ = c)
    {i₁ : Fin (N.N a₁ b₁ c₁)} {i : Fin (N.N a b c)} (hi : i₁.val = i.val)
    {j₁ : Fin (N.N b₁ a₁ c₁)} {j : Fin (N.N b a c)} (hj : j₁.val = j.val) :
    Q.R a₁ b₁ c₁ i₁ j₁ = Q.R a b c i j := by
  subst ha; subst hb; subst hc
  rw [Fin.ext hi, Fin.ext hj]

/-- Transport `RSymbols` covariantly along a unit- and multiplicity-preserving bijection
`σ : ι ≃ ι'`. -/
def reindex (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) {P : FSymbols K N}
    (Q : RSymbols P) : RSymbols (P.reindex σ hunit hN) where
  R a' b' c' :=
    (Q.R (σ.symm a') (σ.symm b') (σ.symm c')).submatrix
      (finCongr (FusionRules.N_symm_eq σ hN a' b' c'))
      (finCongr (FusionRules.N_symm_eq σ hN b' a' c'))
  Rinv a' b' c' :=
    (Q.Rinv (σ.symm a') (σ.symm b') (σ.symm c')).submatrix
      (finCongr (FusionRules.N_symm_eq σ hN b' a' c'))
      (finCongr (FusionRules.N_symm_eq σ hN a' b' c'))
  R_mul_Rinv a' b' c' := by
    rw [Matrix.submatrix_mul_equiv, Q.R_mul_Rinv, Matrix.submatrix_one_equiv]
  Rinv_mul_R a' b' c' := by
    rw [Matrix.submatrix_mul_equiv, Q.Rinv_mul_R, Matrix.submatrix_one_equiv]
  hexagon_forward a' b' c' d' e' g' i' j' n' o' := by
    refine Eq.trans ?_ ((Q.hexagon_forward
      (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d') (σ.symm e') (σ.symm g')
      (i'.cast (FusionRules.N_symm_eq σ hN a' b' e'))
      (j'.cast (FusionRules.N_symm_eq σ hN e' c' d'))
      (n'.cast (FusionRules.N_symm_eq σ hN c' a' g'))
      (o'.cast (FusionRules.N_symm_eq σ hN b' g' d'))).trans (Eq.symm ?_))
    · exact Fintype.sum_equiv σ.symm _ _ fun f' ↦
        Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN b' c' f')) _ _ fun _ ↦
          Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN a' f' d')) _ _ fun _ ↦
            Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN f' a' d')) _ _
              fun _ ↦ by simp
    · exact Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN b' a' e')) _ _ fun _ ↦
        Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN a' c' g')) _ _ fun _ ↦ by simp
  hexagon_reverse a' b' c' d' f' g' k' l' n' o' := by
    refine Eq.trans ?_ ((Q.hexagon_reverse
      (σ.symm a') (σ.symm b') (σ.symm c') (σ.symm d') (σ.symm f') (σ.symm g')
      (k'.cast (FusionRules.N_symm_eq σ hN b' c' f'))
      (l'.cast (FusionRules.N_symm_eq σ hN a' f' d'))
      (n'.cast (FusionRules.N_symm_eq σ hN c' a' g'))
      (o'.cast (FusionRules.N_symm_eq σ hN g' b' d'))).trans (Eq.symm ?_))
    · exact Fintype.sum_equiv σ.symm _ _ fun e' ↦
        Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN a' b' e')) _ _ fun _ ↦
          Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN e' c' d')) _ _ fun _ ↦
            Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN c' e' d')) _ _
              fun _ ↦ by simp
    · exact Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN c' b' f')) _ _ fun _ ↦
        Fintype.sum_equiv (finCongr (FusionRules.N_symm_eq σ hN a' c' g')) _ _ fun _ ↦ by simp

@[simp]
theorem reindex_R_apply (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) {P : FSymbols K N} (Q : RSymbols P)
    (a' b' c' : ι') (i' : Fin (N'.N a' b' c')) (j' : Fin (N'.N b' a' c')) :
    (Q.reindex σ hunit hN).R a' b' c' i' j' =
      Q.R (σ.symm a') (σ.symm b') (σ.symm c')
        (i'.cast (FusionRules.N_symm_eq σ hN a' b' c'))
        (j'.cast (FusionRules.N_symm_eq σ hN b' a' c')) := by
  simp [reindex]

@[simp]
theorem reindex_Rinv_apply (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) {P : FSymbols K N} (Q : RSymbols P)
    (a' b' c' : ι') (j' : Fin (N'.N b' a' c')) (i' : Fin (N'.N a' b' c')) :
    (Q.reindex σ hunit hN).Rinv a' b' c' j' i' =
      Q.Rinv (σ.symm a') (σ.symm b') (σ.symm c')
        (j'.cast (FusionRules.N_symm_eq σ hN b' a' c'))
        (i'.cast (FusionRules.N_symm_eq σ hN a' b' c')) := by
  simp [reindex]

@[simp]
theorem reindex_refl_cast (hunit : Equiv.refl ι N.unit = N.unit)
    (hN : ∀ a b c, N.N a b c = N.N (Equiv.refl ι a) (Equiv.refl ι b) (Equiv.refl ι c))
    {P : FSymbols K N} (Q : RSymbols P) :
    (Q.reindex (Equiv.refl ι) hunit hN).cast (FSymbols.reindex_refl_apply hunit hN P) = Q := by
  ext a b c i j
  rw [cast_R_apply, reindex_R_apply]
  refine R_cast_of_eq Q rfl rfl rfl ?_ ?_ <;> rfl

@[simp]
theorem reindex_trans_cast (σ : ι ≃ ι') (τ : ι' ≃ ι'')
    (hunit₁ : σ N.unit = N'.unit)
    (hN₁ : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c))
    (hunit₂ : τ N'.unit = N''.unit)
    (hN₂ : ∀ a' b' c', N'.N a' b' c' = N''.N (τ a') (τ b') (τ c'))
    {P : FSymbols K N} (Q : RSymbols P) :
    ((Q.reindex σ hunit₁ hN₁).reindex τ hunit₂ hN₂).cast
        (FSymbols.reindex_trans_apply σ τ hunit₁ hN₁ hunit₂ hN₂ P) =
      Q.reindex (σ.trans τ) (by simp [hunit₁, hunit₂]) (by simp [hN₁, hN₂]) := by
  ext a'' b'' c'' i'' j''
  rw [cast_R_apply, reindex_R_apply, reindex_R_apply, reindex_R_apply]
  refine R_cast_of_eq Q rfl rfl rfl ?_ ?_ <;> rfl

/-- `RSymbols.reindex` along a unit- and multiplicity-preserving bijection as an equivalence. -/
def reindexEquiv (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols K N) :
    RSymbols P ≃ RSymbols (P.reindex σ hunit hN) where
  toFun := reindex σ hunit hN
  invFun Q' :=
    (Q'.reindex σ.symm (by rw [← hunit, σ.symm_apply_apply])
      (FusionRules.N_symm_eq σ hN)).cast (by simp)
  left_inv Q := by
    ext a b c i j
    rw [cast_R_apply, reindex_R_apply, reindex_R_apply]
    refine R_cast_of_eq Q (σ.symm_apply_apply a) (σ.symm_apply_apply b)
      (σ.symm_apply_apply c) ?_ ?_ <;> rfl
  right_inv Q' := by
    ext a' b' c' i' j'
    rw [reindex_R_apply, cast_R_apply, reindex_R_apply]
    refine R_cast_of_eq Q' (σ.apply_symm_apply a') (σ.apply_symm_apply b')
      (σ.apply_symm_apply c') ?_ ?_ <;> rfl

@[simp]
theorem reindexEquiv_apply (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols K N) (Q : RSymbols P) :
    reindexEquiv σ hunit hN P Q = Q.reindex σ hunit hN :=
  (rfl)

@[simp]
theorem reindexEquiv_symm_apply (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) (P : FSymbols K N)
    (Q' : RSymbols (P.reindex σ hunit hN)) :
    (reindexEquiv σ hunit hN P).symm Q' =
      (Q'.reindex σ.symm (by rw [← hunit, σ.symm_apply_apply])
        (FusionRules.N_symm_eq σ hN)).cast (by simp) :=
  (rfl)

/-- Base change of `RSymbols` along a ring homomorphism `f : K →+* L`, applying `f` entrywise to
`R` and `Rinv`. -/
def map (f : K →+* L) {P : FSymbols K N} (Q : RSymbols P) : RSymbols (P.map f) where
  R a b c := (Q.R a b c).map f
  Rinv a b c := (Q.Rinv a b c).map f
  R_mul_Rinv a b c := by
    rw [← Matrix.map_mul, Q.R_mul_Rinv, Matrix.map_one f (map_zero f) (map_one f)]
  Rinv_mul_R a b c := by
    rw [← Matrix.map_mul, Q.Rinv_mul_R, Matrix.map_one f (map_zero f) (map_one f)]
  hexagon_forward a b c d e g i j n o := by
    simpa [Matrix.map_apply, map_sum, map_mul] using
      congrArg f (Q.hexagon_forward a b c d e g i j n o)
  hexagon_reverse a b c d e g k l n o := by
    simpa [Matrix.map_apply, map_sum, map_mul] using
      congrArg f (Q.hexagon_reverse a b c d e g k l n o)

@[simp]
theorem map_R_apply (f : K →+* L) {P : FSymbols K N} (Q : RSymbols P) (a b c : ι)
    (i : Fin (N.N a b c)) (j : Fin (N.N b a c)) :
    (Q.map f).R a b c i j = f (Q.R a b c i j) :=
  (rfl)

@[simp]
theorem map_Rinv_apply (f : K →+* L) {P : FSymbols K N} (Q : RSymbols P) (a b c : ι)
    (j : Fin (N.N b a c)) (i : Fin (N.N a b c)) :
    (Q.map f).Rinv a b c j i = f (Q.Rinv a b c j i) :=
  (rfl)

theorem map_R (f : K →+* L) {P : FSymbols K N} (Q : RSymbols P) (a b c : ι) :
    (Q.map f).R a b c = (Q.R a b c).map f :=
  (rfl)

theorem map_Rinv (f : K →+* L) {P : FSymbols K N} (Q : RSymbols P) (a b c : ι) :
    (Q.map f).Rinv a b c = (Q.Rinv a b c).map f :=
  (rfl)

@[simp]
theorem map_id_cast {P : FSymbols K N} (Q : RSymbols P) :
    (Q.map (RingHom.id K)).cast (FSymbols.map_id_apply P) = Q := by
  ext a b c i j
  simp

@[simp]
theorem map_comp_cast (f : K →+* L) (g : L →+* M) {P : FSymbols K N} (Q : RSymbols P) :
    ((Q.map f).map g).cast (FSymbols.map_comp_apply f g P) = Q.map (g.comp f) := by
  ext a b c i j
  simp

/-- Base change of `RSymbols` along a ring isomorphism `e : K ≃+* L` as an equivalence. -/
def mapRingEquiv (e : K ≃+* L) (P : FSymbols K N) :
    RSymbols P ≃ RSymbols (P.map (e : K →+* L)) where
  toFun := map (e : K →+* L)
  invFun Q' := (Q'.map (e.symm : L →+* K)).cast (by simp)
  left_inv Q := by
    ext a b c i j
    rw [cast_R_apply, map_R_apply, map_R_apply]
    simp
  right_inv Q' := by
    ext a b c i j
    rw [map_R_apply, cast_R_apply, map_R_apply]
    simp

@[simp]
theorem mapRingEquiv_apply (e : K ≃+* L) (P : FSymbols K N) (Q : RSymbols P) :
    mapRingEquiv e P Q = Q.map (e : K →+* L) :=
  (rfl)

@[simp]
theorem mapRingEquiv_symm_apply (e : K ≃+* L) (P : FSymbols K N)
    (Q' : RSymbols (P.map (e : K →+* L))) :
    (mapRingEquiv e P).symm Q' = (Q'.map (e.symm : L →+* K)).cast (by simp) :=
  (rfl)

/-- `RSymbols.reindex` and `RSymbols.map` commute up to `RSymbols.cast` along
`FSymbols.reindex_map_apply`. -/
theorem reindex_map_cast (f : K →+* L) (σ : ι ≃ ι') (hunit : σ N.unit = N'.unit)
    (hN : ∀ a b c, N.N a b c = N'.N (σ a) (σ b) (σ c)) {P : FSymbols K N} (Q : RSymbols P) :
    ((Q.map f).reindex σ hunit hN).cast (FSymbols.reindex_map_apply f σ hunit hN P) =
      (Q.reindex σ hunit hN).map f := by
  ext a' b' c' i' j'
  simp

end ReindexAndMap

end RSymbols

end TauCeti

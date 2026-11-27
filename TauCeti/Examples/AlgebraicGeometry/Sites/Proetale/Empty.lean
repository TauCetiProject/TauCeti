/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Sites.Proetale.EtaleComparison
public import TauCeti.AlgebraicGeometry.Sites.Small

/-!
# The étale and pro-étale sites of the empty scheme

For the empty scheme `X`, every object of the small étale site and of the small pro-étale site
has empty underlying scheme, so the empty sieve covers it and both topologies are the topology
`⊤` in which every sieve covers. Every sheaf on either site, with values in any category, is then
terminal, so between two sheaves there is exactly one morphism: each sheaf category is a point.
This is the empty-scheme Check of SchemeAndStackFoundations §2.10 (the étale and pro-étale
sites).
-/

public section

open CategoryTheory Limits AlgebraicGeometry

universe v u

namespace TauCeti.Examples.ProetaleEmpty

variable (X : Scheme.{u}) [IsEmpty X]

/-- Every étale `X`-scheme over the empty scheme `X` is empty. -/
theorem isEmpty_etale_left (V : X.Etale) : IsEmpty V.left :=
  V.hom.base.hom'.toFun.isEmpty (β := X)

/-- Every weakly étale `X`-scheme over the empty scheme `X` is empty. -/
theorem isEmpty_proEt_left (V : X.ProEt) : IsEmpty V.left :=
  V.hom.base.hom'.toFun.isEmpty (β := X)

/-- On the empty scheme every sieve of the small étale site covers. -/
theorem smallEtaleTopology_eq_top : Scheme.smallEtaleTopology X = ⊤ := by
  rw [GrothendieckTopology.eq_top_iff]
  intro V
  have := isEmpty_etale_left X V
  exact Scheme.bot_mem_smallGrothendieckTopology V

variable (A : Type v) [Category A]

/-- Every étale sheaf on the empty scheme is terminal. -/
noncomputable def isTerminalEtaleSheaf (F : Sheaf (Scheme.smallEtaleTopology X) A) :
    IsTerminal F :=
  Sheaf.isTerminalOfEqTop (smallEtaleTopology_eq_top X) F

/-- Every pro-étale sheaf on the empty scheme is terminal. -/
noncomputable def isTerminalProEtSheaf (F : Sheaf (Scheme.ProEt.topology X) A) :
    IsTerminal F :=
  Sheaf.isTerminalOfEqTop (Scheme.ProEt.topology_eq_top_of_isEmpty X) F

/-- Between two étale sheaves on the empty scheme there is at most one morphism (and there is
one, `(isTerminalEtaleSheaf X A G).from F`). -/
theorem subsingleton_etaleSheafHom (F G : Sheaf (Scheme.smallEtaleTopology X) A) :
    Subsingleton (F ⟶ G) :=
  ⟨fun _ _ ↦ (isTerminalEtaleSheaf X A G).hom_ext _ _⟩

/-- Between two pro-étale sheaves on the empty scheme there is at most one morphism (and there
is one, `(isTerminalProEtSheaf X A G).from F`). -/
theorem subsingleton_proEtSheafHom (F G : Sheaf (Scheme.ProEt.topology X) A) :
    Subsingleton (F ⟶ G) :=
  ⟨fun _ _ ↦ (isTerminalProEtSheaf X A G).hom_ext _ _⟩

end TauCeti.Examples.ProetaleEmpty
